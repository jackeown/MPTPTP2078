%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:53 EST 2020

% Result     : Theorem 9.80s
% Output     : CNFRefutation 9.93s
% Verified   : 
% Statistics : Number of formulae       :  181 ( 738 expanded)
%              Number of leaves         :   31 ( 248 expanded)
%              Depth                    :   16
%              Number of atoms          :  384 (2022 expanded)
%              Number of equality atoms :  155 ( 837 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    6 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_148,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => ( r1_tarski(k2_relat_1(B),A)
         => ( v1_funct_1(B)
            & v1_funct_2(B,k1_relat_1(B),A)
            & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B),A))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_111,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).

tff(f_82,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_99,axiom,(
    ! [A,B] :
      ~ ( ~ ( A = k1_xboole_0
            & B != k1_xboole_0 )
        & ! [C] :
            ( ( v1_relat_1(C)
              & v1_funct_1(C) )
           => ~ ( B = k1_relat_1(C)
                & r1_tarski(k2_relat_1(C),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_funct_1)).

tff(f_74,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_56,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_71,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(A,B)
           => ( r1_tarski(k1_relat_1(A),k1_relat_1(B))
              & r1_tarski(k2_relat_1(A),k2_relat_1(B)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_54,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_103,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_135,axiom,(
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

tff(f_37,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(c_78,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_74,plain,(
    r1_tarski(k2_relat_1('#skF_3'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_15523,plain,(
    ! [C_2163,A_2164,B_2165] :
      ( m1_subset_1(C_2163,k1_zfmisc_1(k2_zfmisc_1(A_2164,B_2165)))
      | ~ r1_tarski(k2_relat_1(C_2163),B_2165)
      | ~ r1_tarski(k1_relat_1(C_2163),A_2164)
      | ~ v1_relat_1(C_2163) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_191,plain,(
    ! [A_56] :
      ( k2_relat_1(A_56) != k1_xboole_0
      | k1_xboole_0 = A_56
      | ~ v1_relat_1(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_210,plain,
    ( k2_relat_1('#skF_3') != k1_xboole_0
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_78,c_191])).

tff(c_211,plain,(
    k2_relat_1('#skF_3') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_210])).

tff(c_76,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_72,plain,
    ( ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2')))
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),'#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_80,plain,
    ( ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2')))
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_72])).

tff(c_212,plain,(
    ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_80])).

tff(c_52,plain,(
    ! [A_20,B_21] :
      ( k1_xboole_0 = A_20
      | v1_relat_1('#skF_1'(A_20,B_21)) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_30,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_42,plain,(
    ! [A_20] : k1_relat_1('#skF_1'(A_20,k1_xboole_0)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_50,plain,(
    ! [A_20] : v1_relat_1('#skF_1'(A_20,k1_xboole_0)) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_135,plain,(
    ! [A_49] :
      ( k1_relat_1(A_49) != k1_xboole_0
      | k1_xboole_0 = A_49
      | ~ v1_relat_1(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_141,plain,(
    ! [A_20] :
      ( k1_relat_1('#skF_1'(A_20,k1_xboole_0)) != k1_xboole_0
      | '#skF_1'(A_20,k1_xboole_0) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_50,c_135])).

tff(c_154,plain,(
    ! [A_20] : '#skF_1'(A_20,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_141])).

tff(c_38,plain,(
    ! [A_20] : r1_tarski(k2_relat_1('#skF_1'(A_20,k1_xboole_0)),A_20) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_161,plain,(
    ! [A_20] : r1_tarski(k2_relat_1(k1_xboole_0),A_20) ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_38])).

tff(c_165,plain,(
    ! [A_20] : r1_tarski(k1_xboole_0,A_20) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_161])).

tff(c_32,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_44,plain,(
    ! [A_20,B_21] :
      ( k1_xboole_0 = A_20
      | k1_relat_1('#skF_1'(A_20,B_21)) = B_21 ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_659,plain,(
    ! [A_98,B_99] :
      ( k1_relat_1('#skF_1'(A_98,B_99)) != k1_xboole_0
      | '#skF_1'(A_98,B_99) = k1_xboole_0
      | k1_xboole_0 = A_98 ) ),
    inference(resolution,[status(thm)],[c_52,c_135])).

tff(c_671,plain,(
    ! [B_100,A_101] :
      ( k1_xboole_0 != B_100
      | '#skF_1'(A_101,B_100) = k1_xboole_0
      | k1_xboole_0 = A_101
      | k1_xboole_0 = A_101 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_659])).

tff(c_151,plain,(
    ! [A_20,B_21] :
      ( k1_relat_1('#skF_1'(A_20,B_21)) != k1_xboole_0
      | '#skF_1'(A_20,B_21) = k1_xboole_0
      | k1_xboole_0 = A_20 ) ),
    inference(resolution,[status(thm)],[c_52,c_135])).

tff(c_677,plain,(
    ! [A_101,B_100] :
      ( k1_relat_1(k1_xboole_0) != k1_xboole_0
      | '#skF_1'(A_101,B_100) = k1_xboole_0
      | k1_xboole_0 = A_101
      | k1_xboole_0 != B_100
      | k1_xboole_0 = A_101
      | k1_xboole_0 = A_101 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_671,c_151])).

tff(c_716,plain,(
    ! [A_101,B_100] :
      ( '#skF_1'(A_101,B_100) = k1_xboole_0
      | k1_xboole_0 != B_100
      | k1_xboole_0 = A_101 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_677])).

tff(c_14,plain,(
    ! [B_7] : k2_zfmisc_1(k1_xboole_0,B_7) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_118,plain,(
    ! [A_40,B_41] : v1_relat_1(k2_zfmisc_1(A_40,B_41)) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_120,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_118])).

tff(c_891,plain,(
    ! [A_120,B_121] :
      ( r1_tarski(k1_relat_1(A_120),k1_relat_1(B_121))
      | ~ r1_tarski(A_120,B_121)
      | ~ v1_relat_1(B_121)
      | ~ v1_relat_1(A_120) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_910,plain,(
    ! [A_120] :
      ( r1_tarski(k1_relat_1(A_120),k1_xboole_0)
      | ~ r1_tarski(A_120,k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_120) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_891])).

tff(c_918,plain,(
    ! [A_122] :
      ( r1_tarski(k1_relat_1(A_122),k1_xboole_0)
      | ~ r1_tarski(A_122,k1_xboole_0)
      | ~ v1_relat_1(A_122) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_120,c_910])).

tff(c_18,plain,(
    ! [A_8,B_9] :
      ( m1_subset_1(A_8,k1_zfmisc_1(B_9))
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_233,plain,(
    ! [B_61,A_62] :
      ( v1_relat_1(B_61)
      | ~ m1_subset_1(B_61,k1_zfmisc_1(A_62))
      | ~ v1_relat_1(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_237,plain,(
    ! [A_8,B_9] :
      ( v1_relat_1(A_8)
      | ~ v1_relat_1(B_9)
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(resolution,[status(thm)],[c_18,c_233])).

tff(c_935,plain,(
    ! [A_122] :
      ( v1_relat_1(k1_relat_1(A_122))
      | ~ v1_relat_1(k1_xboole_0)
      | ~ r1_tarski(A_122,k1_xboole_0)
      | ~ v1_relat_1(A_122) ) ),
    inference(resolution,[status(thm)],[c_918,c_237])).

tff(c_985,plain,(
    ! [A_124] :
      ( v1_relat_1(k1_relat_1(A_124))
      | ~ r1_tarski(A_124,k1_xboole_0)
      | ~ v1_relat_1(A_124) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_120,c_935])).

tff(c_2256,plain,(
    ! [B_200,A_201] :
      ( v1_relat_1(B_200)
      | ~ r1_tarski('#skF_1'(A_201,B_200),k1_xboole_0)
      | ~ v1_relat_1('#skF_1'(A_201,B_200))
      | k1_xboole_0 = A_201 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_985])).

tff(c_2259,plain,(
    ! [B_100,A_101] :
      ( v1_relat_1(B_100)
      | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
      | ~ v1_relat_1('#skF_1'(A_101,B_100))
      | k1_xboole_0 = A_101
      | k1_xboole_0 != B_100
      | k1_xboole_0 = A_101 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_716,c_2256])).

tff(c_5417,plain,(
    ! [B_326,A_327] :
      ( v1_relat_1(B_326)
      | ~ v1_relat_1('#skF_1'(A_327,B_326))
      | k1_xboole_0 != B_326
      | k1_xboole_0 = A_327 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_165,c_2259])).

tff(c_5432,plain,(
    ! [B_21,A_20] :
      ( v1_relat_1(B_21)
      | k1_xboole_0 != B_21
      | k1_xboole_0 = A_20 ) ),
    inference(resolution,[status(thm)],[c_52,c_5417])).

tff(c_5445,plain,(
    ! [A_329] : k1_xboole_0 = A_329 ),
    inference(splitLeft,[status(thm)],[c_5432])).

tff(c_5701,plain,(
    $false ),
    inference(superposition,[status(thm),theory(equality)],[c_5445,c_211])).

tff(c_5705,plain,(
    ! [B_1028] :
      ( v1_relat_1(B_1028)
      | k1_xboole_0 != B_1028 ) ),
    inference(splitRight,[status(thm)],[c_5432])).

tff(c_238,plain,(
    ! [A_63,B_64] :
      ( v1_relat_1(A_63)
      | ~ v1_relat_1(B_64)
      | ~ r1_tarski(A_63,B_64) ) ),
    inference(resolution,[status(thm)],[c_18,c_233])).

tff(c_254,plain,
    ( v1_relat_1(k2_relat_1('#skF_3'))
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_74,c_238])).

tff(c_267,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_254])).

tff(c_5723,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(resolution,[status(thm)],[c_5705,c_267])).

tff(c_1658,plain,(
    ! [C_164,A_165,B_166] :
      ( m1_subset_1(C_164,k1_zfmisc_1(k2_zfmisc_1(A_165,B_166)))
      | ~ r1_tarski(k2_relat_1(C_164),B_166)
      | ~ r1_tarski(k1_relat_1(C_164),A_165)
      | ~ v1_relat_1(C_164) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_16,plain,(
    ! [A_8,B_9] :
      ( r1_tarski(A_8,B_9)
      | ~ m1_subset_1(A_8,k1_zfmisc_1(B_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_7390,plain,(
    ! [C_1107,A_1108,B_1109] :
      ( r1_tarski(C_1107,k2_zfmisc_1(A_1108,B_1109))
      | ~ r1_tarski(k2_relat_1(C_1107),B_1109)
      | ~ r1_tarski(k1_relat_1(C_1107),A_1108)
      | ~ v1_relat_1(C_1107) ) ),
    inference(resolution,[status(thm)],[c_1658,c_16])).

tff(c_7426,plain,(
    ! [A_1108] :
      ( r1_tarski('#skF_3',k2_zfmisc_1(A_1108,'#skF_2'))
      | ~ r1_tarski(k1_relat_1('#skF_3'),A_1108)
      | ~ v1_relat_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_74,c_7390])).

tff(c_7455,plain,(
    ! [A_1110] :
      ( r1_tarski('#skF_3',k2_zfmisc_1(A_1110,'#skF_2'))
      | ~ r1_tarski(k1_relat_1('#skF_3'),A_1110) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_7426])).

tff(c_7494,plain,(
    r1_tarski('#skF_3',k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2')) ),
    inference(resolution,[status(thm)],[c_6,c_7455])).

tff(c_813,plain,(
    ! [A_108,B_109,C_110] :
      ( k1_relset_1(A_108,B_109,C_110) = k1_relat_1(C_110)
      | ~ m1_subset_1(C_110,k1_zfmisc_1(k2_zfmisc_1(A_108,B_109))) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_824,plain,(
    ! [A_108,B_109,A_8] :
      ( k1_relset_1(A_108,B_109,A_8) = k1_relat_1(A_8)
      | ~ r1_tarski(A_8,k2_zfmisc_1(A_108,B_109)) ) ),
    inference(resolution,[status(thm)],[c_18,c_813])).

tff(c_7534,plain,(
    k1_relset_1(k1_relat_1('#skF_3'),'#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_7494,c_824])).

tff(c_2239,plain,(
    ! [B_197,C_198,A_199] :
      ( k1_xboole_0 = B_197
      | v1_funct_2(C_198,A_199,B_197)
      | k1_relset_1(A_199,B_197,C_198) != A_199
      | ~ m1_subset_1(C_198,k1_zfmisc_1(k2_zfmisc_1(A_199,B_197))) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_8096,plain,(
    ! [B_1127,A_1128,A_1129] :
      ( k1_xboole_0 = B_1127
      | v1_funct_2(A_1128,A_1129,B_1127)
      | k1_relset_1(A_1129,B_1127,A_1128) != A_1129
      | ~ r1_tarski(A_1128,k2_zfmisc_1(A_1129,B_1127)) ) ),
    inference(resolution,[status(thm)],[c_18,c_2239])).

tff(c_8102,plain,
    ( k1_xboole_0 = '#skF_2'
    | v1_funct_2('#skF_3',k1_relat_1('#skF_3'),'#skF_2')
    | k1_relset_1(k1_relat_1('#skF_3'),'#skF_2','#skF_3') != k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_7494,c_8096])).

tff(c_8150,plain,
    ( k1_xboole_0 = '#skF_2'
    | v1_funct_2('#skF_3',k1_relat_1('#skF_3'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7534,c_8102])).

tff(c_8152,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_212,c_5723,c_8150])).

tff(c_8153,plain,(
    v1_relat_1(k2_relat_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_254])).

tff(c_36,plain,(
    ! [A_19] :
      ( k1_relat_1(A_19) != k1_xboole_0
      | k1_xboole_0 = A_19
      | ~ v1_relat_1(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_8168,plain,
    ( k1_relat_1(k2_relat_1('#skF_3')) != k1_xboole_0
    | k2_relat_1('#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8153,c_36])).

tff(c_8174,plain,(
    k1_relat_1(k2_relat_1('#skF_3')) != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_211,c_8168])).

tff(c_9926,plain,(
    ! [C_1245,A_1246,B_1247] :
      ( m1_subset_1(C_1245,k1_zfmisc_1(k2_zfmisc_1(A_1246,B_1247)))
      | ~ r1_tarski(k2_relat_1(C_1245),B_1247)
      | ~ r1_tarski(k1_relat_1(C_1245),A_1246)
      | ~ v1_relat_1(C_1245) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_11697,plain,(
    ! [C_1997,A_1998,B_1999] :
      ( r1_tarski(C_1997,k2_zfmisc_1(A_1998,B_1999))
      | ~ r1_tarski(k2_relat_1(C_1997),B_1999)
      | ~ r1_tarski(k1_relat_1(C_1997),A_1998)
      | ~ v1_relat_1(C_1997) ) ),
    inference(resolution,[status(thm)],[c_9926,c_16])).

tff(c_11728,plain,(
    ! [A_1998] :
      ( r1_tarski('#skF_3',k2_zfmisc_1(A_1998,'#skF_2'))
      | ~ r1_tarski(k1_relat_1('#skF_3'),A_1998)
      | ~ v1_relat_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_74,c_11697])).

tff(c_11756,plain,(
    ! [A_2000] :
      ( r1_tarski('#skF_3',k2_zfmisc_1(A_2000,'#skF_2'))
      | ~ r1_tarski(k1_relat_1('#skF_3'),A_2000) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_11728])).

tff(c_11790,plain,(
    r1_tarski('#skF_3',k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2')) ),
    inference(resolution,[status(thm)],[c_6,c_11756])).

tff(c_8497,plain,(
    ! [A_1158,B_1159,C_1160] :
      ( k1_relset_1(A_1158,B_1159,C_1160) = k1_relat_1(C_1160)
      | ~ m1_subset_1(C_1160,k1_zfmisc_1(k2_zfmisc_1(A_1158,B_1159))) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_8508,plain,(
    ! [A_1158,B_1159,A_8] :
      ( k1_relset_1(A_1158,B_1159,A_8) = k1_relat_1(A_8)
      | ~ r1_tarski(A_8,k2_zfmisc_1(A_1158,B_1159)) ) ),
    inference(resolution,[status(thm)],[c_18,c_8497])).

tff(c_11811,plain,(
    k1_relset_1(k1_relat_1('#skF_3'),'#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_11790,c_8508])).

tff(c_10735,plain,(
    ! [B_1952,C_1953,A_1954] :
      ( k1_xboole_0 = B_1952
      | v1_funct_2(C_1953,A_1954,B_1952)
      | k1_relset_1(A_1954,B_1952,C_1953) != A_1954
      | ~ m1_subset_1(C_1953,k1_zfmisc_1(k2_zfmisc_1(A_1954,B_1952))) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_13462,plain,(
    ! [B_2041,A_2042,A_2043] :
      ( k1_xboole_0 = B_2041
      | v1_funct_2(A_2042,A_2043,B_2041)
      | k1_relset_1(A_2043,B_2041,A_2042) != A_2043
      | ~ r1_tarski(A_2042,k2_zfmisc_1(A_2043,B_2041)) ) ),
    inference(resolution,[status(thm)],[c_18,c_10735])).

tff(c_13481,plain,
    ( k1_xboole_0 = '#skF_2'
    | v1_funct_2('#skF_3',k1_relat_1('#skF_3'),'#skF_2')
    | k1_relset_1(k1_relat_1('#skF_3'),'#skF_2','#skF_3') != k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_11790,c_13462])).

tff(c_13524,plain,
    ( k1_xboole_0 = '#skF_2'
    | v1_funct_2('#skF_3',k1_relat_1('#skF_3'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11811,c_13481])).

tff(c_13525,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_212,c_13524])).

tff(c_8418,plain,(
    ! [A_1154,B_1155] :
      ( k1_relat_1('#skF_1'(A_1154,B_1155)) != k1_xboole_0
      | '#skF_1'(A_1154,B_1155) = k1_xboole_0
      | k1_xboole_0 = A_1154 ) ),
    inference(resolution,[status(thm)],[c_52,c_135])).

tff(c_8430,plain,(
    ! [B_1156,A_1157] :
      ( k1_xboole_0 != B_1156
      | '#skF_1'(A_1157,B_1156) = k1_xboole_0
      | k1_xboole_0 = A_1157
      | k1_xboole_0 = A_1157 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_8418])).

tff(c_8436,plain,(
    ! [A_1157,B_1156] :
      ( k1_relat_1(k1_xboole_0) != k1_xboole_0
      | '#skF_1'(A_1157,B_1156) = k1_xboole_0
      | k1_xboole_0 = A_1157
      | k1_xboole_0 != B_1156
      | k1_xboole_0 = A_1157
      | k1_xboole_0 = A_1157 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8430,c_151])).

tff(c_8479,plain,(
    ! [A_1157,B_1156] :
      ( '#skF_1'(A_1157,B_1156) = k1_xboole_0
      | k1_xboole_0 != B_1156
      | k1_xboole_0 = A_1157 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_8436])).

tff(c_40,plain,(
    ! [A_20,B_21] :
      ( k1_xboole_0 = A_20
      | r1_tarski(k2_relat_1('#skF_1'(A_20,B_21)),A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_8193,plain,(
    ! [A_1132,C_1133,B_1134] :
      ( r1_tarski(A_1132,C_1133)
      | ~ r1_tarski(B_1134,C_1133)
      | ~ r1_tarski(A_1132,B_1134) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_8242,plain,(
    ! [A_1138] :
      ( r1_tarski(A_1138,'#skF_2')
      | ~ r1_tarski(A_1138,k2_relat_1('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_74,c_8193])).

tff(c_8246,plain,(
    ! [B_21] :
      ( r1_tarski(k2_relat_1('#skF_1'(k2_relat_1('#skF_3'),B_21)),'#skF_2')
      | k2_relat_1('#skF_3') = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_40,c_8242])).

tff(c_8262,plain,(
    ! [B_1139] : r1_tarski(k2_relat_1('#skF_1'(k2_relat_1('#skF_3'),B_1139)),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_211,c_8246])).

tff(c_8,plain,(
    ! [A_3,C_5,B_4] :
      ( r1_tarski(A_3,C_5)
      | ~ r1_tarski(B_4,C_5)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_8351,plain,(
    ! [A_1145,B_1146] :
      ( r1_tarski(A_1145,'#skF_2')
      | ~ r1_tarski(A_1145,k2_relat_1('#skF_1'(k2_relat_1('#skF_3'),B_1146))) ) ),
    inference(resolution,[status(thm)],[c_8262,c_8])).

tff(c_9970,plain,(
    ! [B_1249,B_1250] :
      ( r1_tarski(k2_relat_1('#skF_1'(k2_relat_1('#skF_1'(k2_relat_1('#skF_3'),B_1249)),B_1250)),'#skF_2')
      | k2_relat_1('#skF_1'(k2_relat_1('#skF_3'),B_1249)) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_40,c_8351])).

tff(c_9981,plain,(
    ! [B_1250,B_1156] :
      ( r1_tarski(k2_relat_1('#skF_1'(k2_relat_1(k1_xboole_0),B_1250)),'#skF_2')
      | k2_relat_1('#skF_1'(k2_relat_1('#skF_3'),B_1156)) = k1_xboole_0
      | k1_xboole_0 != B_1156
      | k2_relat_1('#skF_3') = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8479,c_9970])).

tff(c_9998,plain,(
    ! [B_1250,B_1156] :
      ( r1_tarski(k2_relat_1('#skF_1'(k1_xboole_0,B_1250)),'#skF_2')
      | k2_relat_1('#skF_1'(k2_relat_1('#skF_3'),B_1156)) = k1_xboole_0
      | k1_xboole_0 != B_1156
      | k2_relat_1('#skF_3') = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_9981])).

tff(c_9999,plain,(
    ! [B_1250,B_1156] :
      ( r1_tarski(k2_relat_1('#skF_1'(k1_xboole_0,B_1250)),'#skF_2')
      | k2_relat_1('#skF_1'(k2_relat_1('#skF_3'),B_1156)) = k1_xboole_0
      | k1_xboole_0 != B_1156 ) ),
    inference(negUnitSimplification,[status(thm)],[c_211,c_9998])).

tff(c_10457,plain,(
    ! [B_1948] :
      ( k2_relat_1('#skF_1'(k2_relat_1('#skF_3'),B_1948)) = k1_xboole_0
      | k1_xboole_0 != B_1948 ) ),
    inference(splitLeft,[status(thm)],[c_9999])).

tff(c_8177,plain,(
    ! [B_1130,A_1131] :
      ( B_1130 = A_1131
      | ~ r1_tarski(B_1130,A_1131)
      | ~ r1_tarski(A_1131,B_1130) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_8186,plain,(
    ! [A_20,B_21] :
      ( k2_relat_1('#skF_1'(A_20,B_21)) = A_20
      | ~ r1_tarski(A_20,k2_relat_1('#skF_1'(A_20,B_21)))
      | k1_xboole_0 = A_20 ) ),
    inference(resolution,[status(thm)],[c_40,c_8177])).

tff(c_10468,plain,(
    ! [B_1948] :
      ( k2_relat_1('#skF_1'(k2_relat_1('#skF_3'),B_1948)) = k2_relat_1('#skF_3')
      | ~ r1_tarski(k2_relat_1('#skF_3'),k1_xboole_0)
      | k2_relat_1('#skF_3') = k1_xboole_0
      | k1_xboole_0 != B_1948 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10457,c_8186])).

tff(c_10563,plain,(
    ! [B_1948] :
      ( k2_relat_1('#skF_1'(k2_relat_1('#skF_3'),B_1948)) = k2_relat_1('#skF_3')
      | ~ r1_tarski(k2_relat_1('#skF_3'),k1_xboole_0)
      | k1_xboole_0 != B_1948 ) ),
    inference(negUnitSimplification,[status(thm)],[c_211,c_10468])).

tff(c_10882,plain,(
    ~ r1_tarski(k2_relat_1('#skF_3'),k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_10563])).

tff(c_13570,plain,(
    ~ r1_tarski(k2_relat_1('#skF_3'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_13525,c_10882])).

tff(c_13645,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_13570])).

tff(c_13647,plain,(
    r1_tarski(k2_relat_1('#skF_3'),k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_10563])).

tff(c_8968,plain,(
    ! [A_1195,B_1196] :
      ( r1_tarski(k1_relat_1(A_1195),k1_relat_1(B_1196))
      | ~ r1_tarski(A_1195,B_1196)
      | ~ v1_relat_1(B_1196)
      | ~ v1_relat_1(A_1195) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_8987,plain,(
    ! [A_1195] :
      ( r1_tarski(k1_relat_1(A_1195),k1_xboole_0)
      | ~ r1_tarski(A_1195,k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_1195) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_8968])).

tff(c_8995,plain,(
    ! [A_1197] :
      ( r1_tarski(k1_relat_1(A_1197),k1_xboole_0)
      | ~ r1_tarski(A_1197,k1_xboole_0)
      | ~ v1_relat_1(A_1197) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_120,c_8987])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_9011,plain,(
    ! [A_1197] :
      ( k1_relat_1(A_1197) = k1_xboole_0
      | ~ r1_tarski(k1_xboole_0,k1_relat_1(A_1197))
      | ~ r1_tarski(A_1197,k1_xboole_0)
      | ~ v1_relat_1(A_1197) ) ),
    inference(resolution,[status(thm)],[c_8995,c_2])).

tff(c_9029,plain,(
    ! [A_1197] :
      ( k1_relat_1(A_1197) = k1_xboole_0
      | ~ r1_tarski(A_1197,k1_xboole_0)
      | ~ v1_relat_1(A_1197) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_165,c_9011])).

tff(c_13652,plain,
    ( k1_relat_1(k2_relat_1('#skF_3')) = k1_xboole_0
    | ~ v1_relat_1(k2_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_13647,c_9029])).

tff(c_13677,plain,(
    k1_relat_1(k2_relat_1('#skF_3')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8153,c_13652])).

tff(c_13679,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_8174,c_13677])).

tff(c_13680,plain,(
    ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_80])).

tff(c_15534,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_3'),'#skF_2')
    | ~ r1_tarski(k1_relat_1('#skF_3'),k1_relat_1('#skF_3'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_15523,c_13680])).

tff(c_15552,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_6,c_74,c_15534])).

tff(c_15553,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_210])).

tff(c_15567,plain,(
    k1_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_15553,c_15553,c_32])).

tff(c_160,plain,
    ( k1_relat_1('#skF_3') != k1_xboole_0
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_78,c_135])).

tff(c_182,plain,(
    k1_relat_1('#skF_3') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_160])).

tff(c_15556,plain,(
    k1_relat_1('#skF_3') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_15553,c_182])).

tff(c_15588,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_15567,c_15556])).

tff(c_15589,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_160])).

tff(c_15608,plain,(
    ! [A_20] : r1_tarski('#skF_3',A_20) ),
    inference(demodulation,[status(thm),theory(equality)],[c_15589,c_165])).

tff(c_15590,plain,(
    k1_relat_1('#skF_3') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_160])).

tff(c_15610,plain,(
    k1_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_15589,c_15590])).

tff(c_15904,plain,(
    ! [A_2207,B_2208,C_2209] :
      ( k1_relset_1(A_2207,B_2208,C_2209) = k1_relat_1(C_2209)
      | ~ m1_subset_1(C_2209,k1_zfmisc_1(k2_zfmisc_1(A_2207,B_2208))) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_15996,plain,(
    ! [A_2222,B_2223,A_2224] :
      ( k1_relset_1(A_2222,B_2223,A_2224) = k1_relat_1(A_2224)
      | ~ r1_tarski(A_2224,k2_zfmisc_1(A_2222,B_2223)) ) ),
    inference(resolution,[status(thm)],[c_18,c_15904])).

tff(c_16013,plain,(
    ! [A_2222,B_2223] : k1_relset_1(A_2222,B_2223,'#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_15608,c_15996])).

tff(c_16021,plain,(
    ! [A_2222,B_2223] : k1_relset_1(A_2222,B_2223,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_15610,c_16013])).

tff(c_12,plain,(
    ! [A_6] : k2_zfmisc_1(A_6,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_60,plain,(
    ! [A_33] :
      ( v1_funct_2(k1_xboole_0,A_33,k1_xboole_0)
      | k1_xboole_0 = A_33
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(A_33,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_84,plain,(
    ! [A_33] :
      ( v1_funct_2(k1_xboole_0,A_33,k1_xboole_0)
      | k1_xboole_0 = A_33
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_60])).

tff(c_15881,plain,(
    ! [A_33] :
      ( v1_funct_2('#skF_3',A_33,'#skF_3')
      | A_33 = '#skF_3'
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_15589,c_15589,c_15589,c_15589,c_15589,c_84])).

tff(c_15882,plain,(
    ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_15881])).

tff(c_15885,plain,(
    ~ r1_tarski('#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_18,c_15882])).

tff(c_15889,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_15885])).

tff(c_15891,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_15881])).

tff(c_64,plain,(
    ! [C_35,B_34] :
      ( v1_funct_2(C_35,k1_xboole_0,B_34)
      | k1_relset_1(k1_xboole_0,B_34,C_35) != k1_xboole_0
      | ~ m1_subset_1(C_35,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_34))) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_82,plain,(
    ! [C_35,B_34] :
      ( v1_funct_2(C_35,k1_xboole_0,B_34)
      | k1_relset_1(k1_xboole_0,B_34,C_35) != k1_xboole_0
      | ~ m1_subset_1(C_35,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_64])).

tff(c_16443,plain,(
    ! [C_2248,B_2249] :
      ( v1_funct_2(C_2248,'#skF_3',B_2249)
      | k1_relset_1('#skF_3',B_2249,C_2248) != '#skF_3'
      | ~ m1_subset_1(C_2248,k1_zfmisc_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_15589,c_15589,c_15589,c_15589,c_82])).

tff(c_16445,plain,(
    ! [B_2249] :
      ( v1_funct_2('#skF_3','#skF_3',B_2249)
      | k1_relset_1('#skF_3',B_2249,'#skF_3') != '#skF_3' ) ),
    inference(resolution,[status(thm)],[c_15891,c_16443])).

tff(c_16451,plain,(
    ! [B_2249] : v1_funct_2('#skF_3','#skF_3',B_2249) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16021,c_16445])).

tff(c_15616,plain,
    ( ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_15610,c_15610,c_80])).

tff(c_15617,plain,(
    ~ v1_funct_2('#skF_3','#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_15616])).

tff(c_16455,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16451,c_15617])).

tff(c_16456,plain,(
    ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_15616])).

tff(c_16466,plain,(
    ~ r1_tarski('#skF_3',k2_zfmisc_1('#skF_3','#skF_2')) ),
    inference(resolution,[status(thm)],[c_18,c_16456])).

tff(c_16470,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_15608,c_16466])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n010.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 09:20:59 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.80/3.55  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.93/3.57  
% 9.93/3.57  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.93/3.57  %$ v1_funct_2 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 9.93/3.57  
% 9.93/3.57  %Foreground sorts:
% 9.93/3.57  
% 9.93/3.57  
% 9.93/3.57  %Background operators:
% 9.93/3.57  
% 9.93/3.57  
% 9.93/3.57  %Foreground operators:
% 9.93/3.57  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 9.93/3.57  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.93/3.57  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 9.93/3.57  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 9.93/3.57  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 9.93/3.57  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 9.93/3.57  tff('#skF_2', type, '#skF_2': $i).
% 9.93/3.57  tff('#skF_3', type, '#skF_3': $i).
% 9.93/3.57  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 9.93/3.57  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 9.93/3.57  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.93/3.57  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 9.93/3.57  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 9.93/3.57  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.93/3.57  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 9.93/3.57  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 9.93/3.57  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 9.93/3.57  
% 9.93/3.60  tff(f_148, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(k2_relat_1(B), A) => ((v1_funct_1(B) & v1_funct_2(B, k1_relat_1(B), A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B), A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_funct_2)).
% 9.93/3.60  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 9.93/3.60  tff(f_111, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_relset_1)).
% 9.93/3.60  tff(f_82, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_relat_1)).
% 9.93/3.60  tff(f_99, axiom, (![A, B]: ~(~((A = k1_xboole_0) & ~(B = k1_xboole_0)) & (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => ~((B = k1_relat_1(C)) & r1_tarski(k2_relat_1(C), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_funct_1)).
% 9.93/3.60  tff(f_74, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 9.93/3.60  tff(f_43, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 9.93/3.60  tff(f_56, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 9.93/3.60  tff(f_71, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => (r1_tarski(k1_relat_1(A), k1_relat_1(B)) & r1_tarski(k2_relat_1(A), k2_relat_1(B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_relat_1)).
% 9.93/3.60  tff(f_47, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 9.93/3.60  tff(f_54, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 9.93/3.60  tff(f_103, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 9.93/3.60  tff(f_135, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 9.93/3.60  tff(f_37, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 9.93/3.60  tff(c_78, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_148])).
% 9.93/3.60  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.93/3.60  tff(c_74, plain, (r1_tarski(k2_relat_1('#skF_3'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_148])).
% 9.93/3.60  tff(c_15523, plain, (![C_2163, A_2164, B_2165]: (m1_subset_1(C_2163, k1_zfmisc_1(k2_zfmisc_1(A_2164, B_2165))) | ~r1_tarski(k2_relat_1(C_2163), B_2165) | ~r1_tarski(k1_relat_1(C_2163), A_2164) | ~v1_relat_1(C_2163))), inference(cnfTransformation, [status(thm)], [f_111])).
% 9.93/3.60  tff(c_191, plain, (![A_56]: (k2_relat_1(A_56)!=k1_xboole_0 | k1_xboole_0=A_56 | ~v1_relat_1(A_56))), inference(cnfTransformation, [status(thm)], [f_82])).
% 9.93/3.60  tff(c_210, plain, (k2_relat_1('#skF_3')!=k1_xboole_0 | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_78, c_191])).
% 9.93/3.60  tff(c_211, plain, (k2_relat_1('#skF_3')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_210])).
% 9.93/3.60  tff(c_76, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_148])).
% 9.93/3.60  tff(c_72, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2'))) | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), '#skF_2') | ~v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_148])).
% 9.93/3.60  tff(c_80, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2'))) | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_72])).
% 9.93/3.60  tff(c_212, plain, (~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), '#skF_2')), inference(splitLeft, [status(thm)], [c_80])).
% 9.93/3.60  tff(c_52, plain, (![A_20, B_21]: (k1_xboole_0=A_20 | v1_relat_1('#skF_1'(A_20, B_21)))), inference(cnfTransformation, [status(thm)], [f_99])).
% 9.93/3.60  tff(c_30, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_74])).
% 9.93/3.60  tff(c_42, plain, (![A_20]: (k1_relat_1('#skF_1'(A_20, k1_xboole_0))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_99])).
% 9.93/3.60  tff(c_50, plain, (![A_20]: (v1_relat_1('#skF_1'(A_20, k1_xboole_0)))), inference(cnfTransformation, [status(thm)], [f_99])).
% 9.93/3.60  tff(c_135, plain, (![A_49]: (k1_relat_1(A_49)!=k1_xboole_0 | k1_xboole_0=A_49 | ~v1_relat_1(A_49))), inference(cnfTransformation, [status(thm)], [f_82])).
% 9.93/3.60  tff(c_141, plain, (![A_20]: (k1_relat_1('#skF_1'(A_20, k1_xboole_0))!=k1_xboole_0 | '#skF_1'(A_20, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_50, c_135])).
% 9.93/3.60  tff(c_154, plain, (![A_20]: ('#skF_1'(A_20, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_42, c_141])).
% 9.93/3.60  tff(c_38, plain, (![A_20]: (r1_tarski(k2_relat_1('#skF_1'(A_20, k1_xboole_0)), A_20))), inference(cnfTransformation, [status(thm)], [f_99])).
% 9.93/3.60  tff(c_161, plain, (![A_20]: (r1_tarski(k2_relat_1(k1_xboole_0), A_20))), inference(demodulation, [status(thm), theory('equality')], [c_154, c_38])).
% 9.93/3.60  tff(c_165, plain, (![A_20]: (r1_tarski(k1_xboole_0, A_20))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_161])).
% 9.93/3.60  tff(c_32, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_74])).
% 9.93/3.60  tff(c_44, plain, (![A_20, B_21]: (k1_xboole_0=A_20 | k1_relat_1('#skF_1'(A_20, B_21))=B_21)), inference(cnfTransformation, [status(thm)], [f_99])).
% 9.93/3.60  tff(c_659, plain, (![A_98, B_99]: (k1_relat_1('#skF_1'(A_98, B_99))!=k1_xboole_0 | '#skF_1'(A_98, B_99)=k1_xboole_0 | k1_xboole_0=A_98)), inference(resolution, [status(thm)], [c_52, c_135])).
% 9.93/3.60  tff(c_671, plain, (![B_100, A_101]: (k1_xboole_0!=B_100 | '#skF_1'(A_101, B_100)=k1_xboole_0 | k1_xboole_0=A_101 | k1_xboole_0=A_101)), inference(superposition, [status(thm), theory('equality')], [c_44, c_659])).
% 9.93/3.60  tff(c_151, plain, (![A_20, B_21]: (k1_relat_1('#skF_1'(A_20, B_21))!=k1_xboole_0 | '#skF_1'(A_20, B_21)=k1_xboole_0 | k1_xboole_0=A_20)), inference(resolution, [status(thm)], [c_52, c_135])).
% 9.93/3.60  tff(c_677, plain, (![A_101, B_100]: (k1_relat_1(k1_xboole_0)!=k1_xboole_0 | '#skF_1'(A_101, B_100)=k1_xboole_0 | k1_xboole_0=A_101 | k1_xboole_0!=B_100 | k1_xboole_0=A_101 | k1_xboole_0=A_101)), inference(superposition, [status(thm), theory('equality')], [c_671, c_151])).
% 9.93/3.60  tff(c_716, plain, (![A_101, B_100]: ('#skF_1'(A_101, B_100)=k1_xboole_0 | k1_xboole_0!=B_100 | k1_xboole_0=A_101)), inference(demodulation, [status(thm), theory('equality')], [c_32, c_677])).
% 9.93/3.60  tff(c_14, plain, (![B_7]: (k2_zfmisc_1(k1_xboole_0, B_7)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_43])).
% 9.93/3.60  tff(c_118, plain, (![A_40, B_41]: (v1_relat_1(k2_zfmisc_1(A_40, B_41)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 9.93/3.60  tff(c_120, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_14, c_118])).
% 9.93/3.60  tff(c_891, plain, (![A_120, B_121]: (r1_tarski(k1_relat_1(A_120), k1_relat_1(B_121)) | ~r1_tarski(A_120, B_121) | ~v1_relat_1(B_121) | ~v1_relat_1(A_120))), inference(cnfTransformation, [status(thm)], [f_71])).
% 9.93/3.60  tff(c_910, plain, (![A_120]: (r1_tarski(k1_relat_1(A_120), k1_xboole_0) | ~r1_tarski(A_120, k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_120))), inference(superposition, [status(thm), theory('equality')], [c_32, c_891])).
% 9.93/3.60  tff(c_918, plain, (![A_122]: (r1_tarski(k1_relat_1(A_122), k1_xboole_0) | ~r1_tarski(A_122, k1_xboole_0) | ~v1_relat_1(A_122))), inference(demodulation, [status(thm), theory('equality')], [c_120, c_910])).
% 9.93/3.60  tff(c_18, plain, (![A_8, B_9]: (m1_subset_1(A_8, k1_zfmisc_1(B_9)) | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_47])).
% 9.93/3.60  tff(c_233, plain, (![B_61, A_62]: (v1_relat_1(B_61) | ~m1_subset_1(B_61, k1_zfmisc_1(A_62)) | ~v1_relat_1(A_62))), inference(cnfTransformation, [status(thm)], [f_54])).
% 9.93/3.60  tff(c_237, plain, (![A_8, B_9]: (v1_relat_1(A_8) | ~v1_relat_1(B_9) | ~r1_tarski(A_8, B_9))), inference(resolution, [status(thm)], [c_18, c_233])).
% 9.93/3.60  tff(c_935, plain, (![A_122]: (v1_relat_1(k1_relat_1(A_122)) | ~v1_relat_1(k1_xboole_0) | ~r1_tarski(A_122, k1_xboole_0) | ~v1_relat_1(A_122))), inference(resolution, [status(thm)], [c_918, c_237])).
% 9.93/3.60  tff(c_985, plain, (![A_124]: (v1_relat_1(k1_relat_1(A_124)) | ~r1_tarski(A_124, k1_xboole_0) | ~v1_relat_1(A_124))), inference(demodulation, [status(thm), theory('equality')], [c_120, c_935])).
% 9.93/3.60  tff(c_2256, plain, (![B_200, A_201]: (v1_relat_1(B_200) | ~r1_tarski('#skF_1'(A_201, B_200), k1_xboole_0) | ~v1_relat_1('#skF_1'(A_201, B_200)) | k1_xboole_0=A_201)), inference(superposition, [status(thm), theory('equality')], [c_44, c_985])).
% 9.93/3.60  tff(c_2259, plain, (![B_100, A_101]: (v1_relat_1(B_100) | ~r1_tarski(k1_xboole_0, k1_xboole_0) | ~v1_relat_1('#skF_1'(A_101, B_100)) | k1_xboole_0=A_101 | k1_xboole_0!=B_100 | k1_xboole_0=A_101)), inference(superposition, [status(thm), theory('equality')], [c_716, c_2256])).
% 9.93/3.60  tff(c_5417, plain, (![B_326, A_327]: (v1_relat_1(B_326) | ~v1_relat_1('#skF_1'(A_327, B_326)) | k1_xboole_0!=B_326 | k1_xboole_0=A_327)), inference(demodulation, [status(thm), theory('equality')], [c_165, c_2259])).
% 9.93/3.60  tff(c_5432, plain, (![B_21, A_20]: (v1_relat_1(B_21) | k1_xboole_0!=B_21 | k1_xboole_0=A_20)), inference(resolution, [status(thm)], [c_52, c_5417])).
% 9.93/3.60  tff(c_5445, plain, (![A_329]: (k1_xboole_0=A_329)), inference(splitLeft, [status(thm)], [c_5432])).
% 9.93/3.60  tff(c_5701, plain, $false, inference(superposition, [status(thm), theory('equality')], [c_5445, c_211])).
% 9.93/3.60  tff(c_5705, plain, (![B_1028]: (v1_relat_1(B_1028) | k1_xboole_0!=B_1028)), inference(splitRight, [status(thm)], [c_5432])).
% 9.93/3.60  tff(c_238, plain, (![A_63, B_64]: (v1_relat_1(A_63) | ~v1_relat_1(B_64) | ~r1_tarski(A_63, B_64))), inference(resolution, [status(thm)], [c_18, c_233])).
% 9.93/3.60  tff(c_254, plain, (v1_relat_1(k2_relat_1('#skF_3')) | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_74, c_238])).
% 9.93/3.60  tff(c_267, plain, (~v1_relat_1('#skF_2')), inference(splitLeft, [status(thm)], [c_254])).
% 9.93/3.60  tff(c_5723, plain, (k1_xboole_0!='#skF_2'), inference(resolution, [status(thm)], [c_5705, c_267])).
% 9.93/3.60  tff(c_1658, plain, (![C_164, A_165, B_166]: (m1_subset_1(C_164, k1_zfmisc_1(k2_zfmisc_1(A_165, B_166))) | ~r1_tarski(k2_relat_1(C_164), B_166) | ~r1_tarski(k1_relat_1(C_164), A_165) | ~v1_relat_1(C_164))), inference(cnfTransformation, [status(thm)], [f_111])).
% 9.93/3.60  tff(c_16, plain, (![A_8, B_9]: (r1_tarski(A_8, B_9) | ~m1_subset_1(A_8, k1_zfmisc_1(B_9)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 9.93/3.60  tff(c_7390, plain, (![C_1107, A_1108, B_1109]: (r1_tarski(C_1107, k2_zfmisc_1(A_1108, B_1109)) | ~r1_tarski(k2_relat_1(C_1107), B_1109) | ~r1_tarski(k1_relat_1(C_1107), A_1108) | ~v1_relat_1(C_1107))), inference(resolution, [status(thm)], [c_1658, c_16])).
% 9.93/3.60  tff(c_7426, plain, (![A_1108]: (r1_tarski('#skF_3', k2_zfmisc_1(A_1108, '#skF_2')) | ~r1_tarski(k1_relat_1('#skF_3'), A_1108) | ~v1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_74, c_7390])).
% 9.93/3.60  tff(c_7455, plain, (![A_1110]: (r1_tarski('#skF_3', k2_zfmisc_1(A_1110, '#skF_2')) | ~r1_tarski(k1_relat_1('#skF_3'), A_1110))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_7426])).
% 9.93/3.60  tff(c_7494, plain, (r1_tarski('#skF_3', k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2'))), inference(resolution, [status(thm)], [c_6, c_7455])).
% 9.93/3.60  tff(c_813, plain, (![A_108, B_109, C_110]: (k1_relset_1(A_108, B_109, C_110)=k1_relat_1(C_110) | ~m1_subset_1(C_110, k1_zfmisc_1(k2_zfmisc_1(A_108, B_109))))), inference(cnfTransformation, [status(thm)], [f_103])).
% 9.93/3.60  tff(c_824, plain, (![A_108, B_109, A_8]: (k1_relset_1(A_108, B_109, A_8)=k1_relat_1(A_8) | ~r1_tarski(A_8, k2_zfmisc_1(A_108, B_109)))), inference(resolution, [status(thm)], [c_18, c_813])).
% 9.93/3.60  tff(c_7534, plain, (k1_relset_1(k1_relat_1('#skF_3'), '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_7494, c_824])).
% 9.93/3.60  tff(c_2239, plain, (![B_197, C_198, A_199]: (k1_xboole_0=B_197 | v1_funct_2(C_198, A_199, B_197) | k1_relset_1(A_199, B_197, C_198)!=A_199 | ~m1_subset_1(C_198, k1_zfmisc_1(k2_zfmisc_1(A_199, B_197))))), inference(cnfTransformation, [status(thm)], [f_135])).
% 9.93/3.60  tff(c_8096, plain, (![B_1127, A_1128, A_1129]: (k1_xboole_0=B_1127 | v1_funct_2(A_1128, A_1129, B_1127) | k1_relset_1(A_1129, B_1127, A_1128)!=A_1129 | ~r1_tarski(A_1128, k2_zfmisc_1(A_1129, B_1127)))), inference(resolution, [status(thm)], [c_18, c_2239])).
% 9.93/3.60  tff(c_8102, plain, (k1_xboole_0='#skF_2' | v1_funct_2('#skF_3', k1_relat_1('#skF_3'), '#skF_2') | k1_relset_1(k1_relat_1('#skF_3'), '#skF_2', '#skF_3')!=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_7494, c_8096])).
% 9.93/3.60  tff(c_8150, plain, (k1_xboole_0='#skF_2' | v1_funct_2('#skF_3', k1_relat_1('#skF_3'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_7534, c_8102])).
% 9.93/3.60  tff(c_8152, plain, $false, inference(negUnitSimplification, [status(thm)], [c_212, c_5723, c_8150])).
% 9.93/3.60  tff(c_8153, plain, (v1_relat_1(k2_relat_1('#skF_3'))), inference(splitRight, [status(thm)], [c_254])).
% 9.93/3.60  tff(c_36, plain, (![A_19]: (k1_relat_1(A_19)!=k1_xboole_0 | k1_xboole_0=A_19 | ~v1_relat_1(A_19))), inference(cnfTransformation, [status(thm)], [f_82])).
% 9.93/3.60  tff(c_8168, plain, (k1_relat_1(k2_relat_1('#skF_3'))!=k1_xboole_0 | k2_relat_1('#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_8153, c_36])).
% 9.93/3.60  tff(c_8174, plain, (k1_relat_1(k2_relat_1('#skF_3'))!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_211, c_8168])).
% 9.93/3.60  tff(c_9926, plain, (![C_1245, A_1246, B_1247]: (m1_subset_1(C_1245, k1_zfmisc_1(k2_zfmisc_1(A_1246, B_1247))) | ~r1_tarski(k2_relat_1(C_1245), B_1247) | ~r1_tarski(k1_relat_1(C_1245), A_1246) | ~v1_relat_1(C_1245))), inference(cnfTransformation, [status(thm)], [f_111])).
% 9.93/3.60  tff(c_11697, plain, (![C_1997, A_1998, B_1999]: (r1_tarski(C_1997, k2_zfmisc_1(A_1998, B_1999)) | ~r1_tarski(k2_relat_1(C_1997), B_1999) | ~r1_tarski(k1_relat_1(C_1997), A_1998) | ~v1_relat_1(C_1997))), inference(resolution, [status(thm)], [c_9926, c_16])).
% 9.93/3.60  tff(c_11728, plain, (![A_1998]: (r1_tarski('#skF_3', k2_zfmisc_1(A_1998, '#skF_2')) | ~r1_tarski(k1_relat_1('#skF_3'), A_1998) | ~v1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_74, c_11697])).
% 9.93/3.60  tff(c_11756, plain, (![A_2000]: (r1_tarski('#skF_3', k2_zfmisc_1(A_2000, '#skF_2')) | ~r1_tarski(k1_relat_1('#skF_3'), A_2000))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_11728])).
% 9.93/3.60  tff(c_11790, plain, (r1_tarski('#skF_3', k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2'))), inference(resolution, [status(thm)], [c_6, c_11756])).
% 9.93/3.60  tff(c_8497, plain, (![A_1158, B_1159, C_1160]: (k1_relset_1(A_1158, B_1159, C_1160)=k1_relat_1(C_1160) | ~m1_subset_1(C_1160, k1_zfmisc_1(k2_zfmisc_1(A_1158, B_1159))))), inference(cnfTransformation, [status(thm)], [f_103])).
% 9.93/3.60  tff(c_8508, plain, (![A_1158, B_1159, A_8]: (k1_relset_1(A_1158, B_1159, A_8)=k1_relat_1(A_8) | ~r1_tarski(A_8, k2_zfmisc_1(A_1158, B_1159)))), inference(resolution, [status(thm)], [c_18, c_8497])).
% 9.93/3.60  tff(c_11811, plain, (k1_relset_1(k1_relat_1('#skF_3'), '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_11790, c_8508])).
% 9.93/3.60  tff(c_10735, plain, (![B_1952, C_1953, A_1954]: (k1_xboole_0=B_1952 | v1_funct_2(C_1953, A_1954, B_1952) | k1_relset_1(A_1954, B_1952, C_1953)!=A_1954 | ~m1_subset_1(C_1953, k1_zfmisc_1(k2_zfmisc_1(A_1954, B_1952))))), inference(cnfTransformation, [status(thm)], [f_135])).
% 9.93/3.60  tff(c_13462, plain, (![B_2041, A_2042, A_2043]: (k1_xboole_0=B_2041 | v1_funct_2(A_2042, A_2043, B_2041) | k1_relset_1(A_2043, B_2041, A_2042)!=A_2043 | ~r1_tarski(A_2042, k2_zfmisc_1(A_2043, B_2041)))), inference(resolution, [status(thm)], [c_18, c_10735])).
% 9.93/3.60  tff(c_13481, plain, (k1_xboole_0='#skF_2' | v1_funct_2('#skF_3', k1_relat_1('#skF_3'), '#skF_2') | k1_relset_1(k1_relat_1('#skF_3'), '#skF_2', '#skF_3')!=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_11790, c_13462])).
% 9.93/3.60  tff(c_13524, plain, (k1_xboole_0='#skF_2' | v1_funct_2('#skF_3', k1_relat_1('#skF_3'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_11811, c_13481])).
% 9.93/3.60  tff(c_13525, plain, (k1_xboole_0='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_212, c_13524])).
% 9.93/3.60  tff(c_8418, plain, (![A_1154, B_1155]: (k1_relat_1('#skF_1'(A_1154, B_1155))!=k1_xboole_0 | '#skF_1'(A_1154, B_1155)=k1_xboole_0 | k1_xboole_0=A_1154)), inference(resolution, [status(thm)], [c_52, c_135])).
% 9.93/3.60  tff(c_8430, plain, (![B_1156, A_1157]: (k1_xboole_0!=B_1156 | '#skF_1'(A_1157, B_1156)=k1_xboole_0 | k1_xboole_0=A_1157 | k1_xboole_0=A_1157)), inference(superposition, [status(thm), theory('equality')], [c_44, c_8418])).
% 9.93/3.60  tff(c_8436, plain, (![A_1157, B_1156]: (k1_relat_1(k1_xboole_0)!=k1_xboole_0 | '#skF_1'(A_1157, B_1156)=k1_xboole_0 | k1_xboole_0=A_1157 | k1_xboole_0!=B_1156 | k1_xboole_0=A_1157 | k1_xboole_0=A_1157)), inference(superposition, [status(thm), theory('equality')], [c_8430, c_151])).
% 9.93/3.60  tff(c_8479, plain, (![A_1157, B_1156]: ('#skF_1'(A_1157, B_1156)=k1_xboole_0 | k1_xboole_0!=B_1156 | k1_xboole_0=A_1157)), inference(demodulation, [status(thm), theory('equality')], [c_32, c_8436])).
% 9.93/3.60  tff(c_40, plain, (![A_20, B_21]: (k1_xboole_0=A_20 | r1_tarski(k2_relat_1('#skF_1'(A_20, B_21)), A_20))), inference(cnfTransformation, [status(thm)], [f_99])).
% 9.93/3.60  tff(c_8193, plain, (![A_1132, C_1133, B_1134]: (r1_tarski(A_1132, C_1133) | ~r1_tarski(B_1134, C_1133) | ~r1_tarski(A_1132, B_1134))), inference(cnfTransformation, [status(thm)], [f_37])).
% 9.93/3.60  tff(c_8242, plain, (![A_1138]: (r1_tarski(A_1138, '#skF_2') | ~r1_tarski(A_1138, k2_relat_1('#skF_3')))), inference(resolution, [status(thm)], [c_74, c_8193])).
% 9.93/3.60  tff(c_8246, plain, (![B_21]: (r1_tarski(k2_relat_1('#skF_1'(k2_relat_1('#skF_3'), B_21)), '#skF_2') | k2_relat_1('#skF_3')=k1_xboole_0)), inference(resolution, [status(thm)], [c_40, c_8242])).
% 9.93/3.60  tff(c_8262, plain, (![B_1139]: (r1_tarski(k2_relat_1('#skF_1'(k2_relat_1('#skF_3'), B_1139)), '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_211, c_8246])).
% 9.93/3.60  tff(c_8, plain, (![A_3, C_5, B_4]: (r1_tarski(A_3, C_5) | ~r1_tarski(B_4, C_5) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_37])).
% 9.93/3.60  tff(c_8351, plain, (![A_1145, B_1146]: (r1_tarski(A_1145, '#skF_2') | ~r1_tarski(A_1145, k2_relat_1('#skF_1'(k2_relat_1('#skF_3'), B_1146))))), inference(resolution, [status(thm)], [c_8262, c_8])).
% 9.93/3.60  tff(c_9970, plain, (![B_1249, B_1250]: (r1_tarski(k2_relat_1('#skF_1'(k2_relat_1('#skF_1'(k2_relat_1('#skF_3'), B_1249)), B_1250)), '#skF_2') | k2_relat_1('#skF_1'(k2_relat_1('#skF_3'), B_1249))=k1_xboole_0)), inference(resolution, [status(thm)], [c_40, c_8351])).
% 9.93/3.60  tff(c_9981, plain, (![B_1250, B_1156]: (r1_tarski(k2_relat_1('#skF_1'(k2_relat_1(k1_xboole_0), B_1250)), '#skF_2') | k2_relat_1('#skF_1'(k2_relat_1('#skF_3'), B_1156))=k1_xboole_0 | k1_xboole_0!=B_1156 | k2_relat_1('#skF_3')=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_8479, c_9970])).
% 9.93/3.60  tff(c_9998, plain, (![B_1250, B_1156]: (r1_tarski(k2_relat_1('#skF_1'(k1_xboole_0, B_1250)), '#skF_2') | k2_relat_1('#skF_1'(k2_relat_1('#skF_3'), B_1156))=k1_xboole_0 | k1_xboole_0!=B_1156 | k2_relat_1('#skF_3')=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_30, c_9981])).
% 9.93/3.60  tff(c_9999, plain, (![B_1250, B_1156]: (r1_tarski(k2_relat_1('#skF_1'(k1_xboole_0, B_1250)), '#skF_2') | k2_relat_1('#skF_1'(k2_relat_1('#skF_3'), B_1156))=k1_xboole_0 | k1_xboole_0!=B_1156)), inference(negUnitSimplification, [status(thm)], [c_211, c_9998])).
% 9.93/3.60  tff(c_10457, plain, (![B_1948]: (k2_relat_1('#skF_1'(k2_relat_1('#skF_3'), B_1948))=k1_xboole_0 | k1_xboole_0!=B_1948)), inference(splitLeft, [status(thm)], [c_9999])).
% 9.93/3.60  tff(c_8177, plain, (![B_1130, A_1131]: (B_1130=A_1131 | ~r1_tarski(B_1130, A_1131) | ~r1_tarski(A_1131, B_1130))), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.93/3.60  tff(c_8186, plain, (![A_20, B_21]: (k2_relat_1('#skF_1'(A_20, B_21))=A_20 | ~r1_tarski(A_20, k2_relat_1('#skF_1'(A_20, B_21))) | k1_xboole_0=A_20)), inference(resolution, [status(thm)], [c_40, c_8177])).
% 9.93/3.60  tff(c_10468, plain, (![B_1948]: (k2_relat_1('#skF_1'(k2_relat_1('#skF_3'), B_1948))=k2_relat_1('#skF_3') | ~r1_tarski(k2_relat_1('#skF_3'), k1_xboole_0) | k2_relat_1('#skF_3')=k1_xboole_0 | k1_xboole_0!=B_1948)), inference(superposition, [status(thm), theory('equality')], [c_10457, c_8186])).
% 9.93/3.60  tff(c_10563, plain, (![B_1948]: (k2_relat_1('#skF_1'(k2_relat_1('#skF_3'), B_1948))=k2_relat_1('#skF_3') | ~r1_tarski(k2_relat_1('#skF_3'), k1_xboole_0) | k1_xboole_0!=B_1948)), inference(negUnitSimplification, [status(thm)], [c_211, c_10468])).
% 9.93/3.60  tff(c_10882, plain, (~r1_tarski(k2_relat_1('#skF_3'), k1_xboole_0)), inference(splitLeft, [status(thm)], [c_10563])).
% 9.93/3.60  tff(c_13570, plain, (~r1_tarski(k2_relat_1('#skF_3'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_13525, c_10882])).
% 9.93/3.60  tff(c_13645, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_74, c_13570])).
% 9.93/3.60  tff(c_13647, plain, (r1_tarski(k2_relat_1('#skF_3'), k1_xboole_0)), inference(splitRight, [status(thm)], [c_10563])).
% 9.93/3.60  tff(c_8968, plain, (![A_1195, B_1196]: (r1_tarski(k1_relat_1(A_1195), k1_relat_1(B_1196)) | ~r1_tarski(A_1195, B_1196) | ~v1_relat_1(B_1196) | ~v1_relat_1(A_1195))), inference(cnfTransformation, [status(thm)], [f_71])).
% 9.93/3.60  tff(c_8987, plain, (![A_1195]: (r1_tarski(k1_relat_1(A_1195), k1_xboole_0) | ~r1_tarski(A_1195, k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_1195))), inference(superposition, [status(thm), theory('equality')], [c_32, c_8968])).
% 9.93/3.60  tff(c_8995, plain, (![A_1197]: (r1_tarski(k1_relat_1(A_1197), k1_xboole_0) | ~r1_tarski(A_1197, k1_xboole_0) | ~v1_relat_1(A_1197))), inference(demodulation, [status(thm), theory('equality')], [c_120, c_8987])).
% 9.93/3.60  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.93/3.60  tff(c_9011, plain, (![A_1197]: (k1_relat_1(A_1197)=k1_xboole_0 | ~r1_tarski(k1_xboole_0, k1_relat_1(A_1197)) | ~r1_tarski(A_1197, k1_xboole_0) | ~v1_relat_1(A_1197))), inference(resolution, [status(thm)], [c_8995, c_2])).
% 9.93/3.60  tff(c_9029, plain, (![A_1197]: (k1_relat_1(A_1197)=k1_xboole_0 | ~r1_tarski(A_1197, k1_xboole_0) | ~v1_relat_1(A_1197))), inference(demodulation, [status(thm), theory('equality')], [c_165, c_9011])).
% 9.93/3.60  tff(c_13652, plain, (k1_relat_1(k2_relat_1('#skF_3'))=k1_xboole_0 | ~v1_relat_1(k2_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_13647, c_9029])).
% 9.93/3.60  tff(c_13677, plain, (k1_relat_1(k2_relat_1('#skF_3'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_8153, c_13652])).
% 9.93/3.60  tff(c_13679, plain, $false, inference(negUnitSimplification, [status(thm)], [c_8174, c_13677])).
% 9.93/3.60  tff(c_13680, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2')))), inference(splitRight, [status(thm)], [c_80])).
% 9.93/3.60  tff(c_15534, plain, (~r1_tarski(k2_relat_1('#skF_3'), '#skF_2') | ~r1_tarski(k1_relat_1('#skF_3'), k1_relat_1('#skF_3')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_15523, c_13680])).
% 9.93/3.60  tff(c_15552, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_78, c_6, c_74, c_15534])).
% 9.93/3.60  tff(c_15553, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_210])).
% 9.93/3.60  tff(c_15567, plain, (k1_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_15553, c_15553, c_32])).
% 9.93/3.60  tff(c_160, plain, (k1_relat_1('#skF_3')!=k1_xboole_0 | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_78, c_135])).
% 9.93/3.60  tff(c_182, plain, (k1_relat_1('#skF_3')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_160])).
% 9.93/3.60  tff(c_15556, plain, (k1_relat_1('#skF_3')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_15553, c_182])).
% 9.93/3.60  tff(c_15588, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_15567, c_15556])).
% 9.93/3.60  tff(c_15589, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_160])).
% 9.93/3.60  tff(c_15608, plain, (![A_20]: (r1_tarski('#skF_3', A_20))), inference(demodulation, [status(thm), theory('equality')], [c_15589, c_165])).
% 9.93/3.60  tff(c_15590, plain, (k1_relat_1('#skF_3')=k1_xboole_0), inference(splitRight, [status(thm)], [c_160])).
% 9.93/3.60  tff(c_15610, plain, (k1_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_15589, c_15590])).
% 9.93/3.60  tff(c_15904, plain, (![A_2207, B_2208, C_2209]: (k1_relset_1(A_2207, B_2208, C_2209)=k1_relat_1(C_2209) | ~m1_subset_1(C_2209, k1_zfmisc_1(k2_zfmisc_1(A_2207, B_2208))))), inference(cnfTransformation, [status(thm)], [f_103])).
% 9.93/3.60  tff(c_15996, plain, (![A_2222, B_2223, A_2224]: (k1_relset_1(A_2222, B_2223, A_2224)=k1_relat_1(A_2224) | ~r1_tarski(A_2224, k2_zfmisc_1(A_2222, B_2223)))), inference(resolution, [status(thm)], [c_18, c_15904])).
% 9.93/3.60  tff(c_16013, plain, (![A_2222, B_2223]: (k1_relset_1(A_2222, B_2223, '#skF_3')=k1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_15608, c_15996])).
% 9.93/3.60  tff(c_16021, plain, (![A_2222, B_2223]: (k1_relset_1(A_2222, B_2223, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_15610, c_16013])).
% 9.93/3.60  tff(c_12, plain, (![A_6]: (k2_zfmisc_1(A_6, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_43])).
% 9.93/3.60  tff(c_60, plain, (![A_33]: (v1_funct_2(k1_xboole_0, A_33, k1_xboole_0) | k1_xboole_0=A_33 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(A_33, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_135])).
% 9.93/3.60  tff(c_84, plain, (![A_33]: (v1_funct_2(k1_xboole_0, A_33, k1_xboole_0) | k1_xboole_0=A_33 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_60])).
% 9.93/3.60  tff(c_15881, plain, (![A_33]: (v1_funct_2('#skF_3', A_33, '#skF_3') | A_33='#skF_3' | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_15589, c_15589, c_15589, c_15589, c_15589, c_84])).
% 9.93/3.60  tff(c_15882, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_15881])).
% 9.93/3.60  tff(c_15885, plain, (~r1_tarski('#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_18, c_15882])).
% 9.93/3.60  tff(c_15889, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_15885])).
% 9.93/3.60  tff(c_15891, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3'))), inference(splitRight, [status(thm)], [c_15881])).
% 9.93/3.60  tff(c_64, plain, (![C_35, B_34]: (v1_funct_2(C_35, k1_xboole_0, B_34) | k1_relset_1(k1_xboole_0, B_34, C_35)!=k1_xboole_0 | ~m1_subset_1(C_35, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_34))))), inference(cnfTransformation, [status(thm)], [f_135])).
% 9.93/3.60  tff(c_82, plain, (![C_35, B_34]: (v1_funct_2(C_35, k1_xboole_0, B_34) | k1_relset_1(k1_xboole_0, B_34, C_35)!=k1_xboole_0 | ~m1_subset_1(C_35, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_64])).
% 9.93/3.60  tff(c_16443, plain, (![C_2248, B_2249]: (v1_funct_2(C_2248, '#skF_3', B_2249) | k1_relset_1('#skF_3', B_2249, C_2248)!='#skF_3' | ~m1_subset_1(C_2248, k1_zfmisc_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_15589, c_15589, c_15589, c_15589, c_82])).
% 9.93/3.60  tff(c_16445, plain, (![B_2249]: (v1_funct_2('#skF_3', '#skF_3', B_2249) | k1_relset_1('#skF_3', B_2249, '#skF_3')!='#skF_3')), inference(resolution, [status(thm)], [c_15891, c_16443])).
% 9.93/3.60  tff(c_16451, plain, (![B_2249]: (v1_funct_2('#skF_3', '#skF_3', B_2249))), inference(demodulation, [status(thm), theory('equality')], [c_16021, c_16445])).
% 9.93/3.60  tff(c_15616, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_15610, c_15610, c_80])).
% 9.93/3.60  tff(c_15617, plain, (~v1_funct_2('#skF_3', '#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_15616])).
% 9.93/3.60  tff(c_16455, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16451, c_15617])).
% 9.93/3.60  tff(c_16456, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitRight, [status(thm)], [c_15616])).
% 9.93/3.60  tff(c_16466, plain, (~r1_tarski('#skF_3', k2_zfmisc_1('#skF_3', '#skF_2'))), inference(resolution, [status(thm)], [c_18, c_16456])).
% 9.93/3.60  tff(c_16470, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_15608, c_16466])).
% 9.93/3.60  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.93/3.60  
% 9.93/3.60  Inference rules
% 9.93/3.60  ----------------------
% 9.93/3.60  #Ref     : 0
% 9.93/3.60  #Sup     : 3667
% 9.93/3.60  #Fact    : 0
% 9.93/3.60  #Define  : 0
% 9.93/3.60  #Split   : 45
% 9.93/3.60  #Chain   : 0
% 9.93/3.60  #Close   : 0
% 9.93/3.60  
% 9.93/3.60  Ordering : KBO
% 9.93/3.60  
% 9.93/3.60  Simplification rules
% 9.93/3.60  ----------------------
% 9.93/3.60  #Subsume      : 1107
% 9.93/3.60  #Demod        : 3239
% 9.93/3.60  #Tautology    : 1232
% 9.93/3.60  #SimpNegUnit  : 169
% 9.93/3.60  #BackRed      : 434
% 9.93/3.60  
% 9.93/3.60  #Partial instantiations: 270
% 9.93/3.60  #Strategies tried      : 1
% 9.93/3.60  
% 9.93/3.60  Timing (in seconds)
% 9.93/3.60  ----------------------
% 9.93/3.60  Preprocessing        : 0.35
% 9.93/3.60  Parsing              : 0.18
% 9.93/3.60  CNF conversion       : 0.02
% 9.93/3.60  Main loop            : 2.43
% 9.93/3.60  Inferencing          : 0.71
% 9.93/3.60  Reduction            : 0.81
% 9.93/3.60  Demodulation         : 0.56
% 9.93/3.60  BG Simplification    : 0.08
% 9.93/3.60  Subsumption          : 0.67
% 9.93/3.60  Abstraction          : 0.11
% 9.93/3.60  MUC search           : 0.00
% 9.93/3.60  Cooper               : 0.00
% 9.93/3.60  Total                : 2.83
% 9.93/3.60  Index Insertion      : 0.00
% 9.93/3.60  Index Deletion       : 0.00
% 9.93/3.60  Index Matching       : 0.00
% 9.93/3.60  BG Taut test         : 0.00
%------------------------------------------------------------------------------
