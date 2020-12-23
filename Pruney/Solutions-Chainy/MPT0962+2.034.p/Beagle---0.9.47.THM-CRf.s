%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:56 EST 2020

% Result     : Theorem 5.76s
% Output     : CNFRefutation 5.76s
% Verified   : 
% Statistics : Number of formulae       :  195 (1798 expanded)
%              Number of leaves         :   34 ( 581 expanded)
%              Depth                    :   16
%              Number of atoms          :  342 (4355 expanded)
%              Number of equality atoms :   90 ( 852 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k6_subset_1 > k4_xboole_0 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff(k6_subset_1,type,(
    k6_subset_1: ( $i * $i ) > $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_108,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => ( r1_tarski(k2_relat_1(B),A)
         => ( v1_funct_1(B)
            & v1_funct_2(B,k1_relat_1(B),A)
            & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B),A))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).

tff(f_40,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_77,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).

tff(f_34,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_58,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_69,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_95,axiom,(
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

tff(f_50,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_54,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_52,axiom,(
    ! [A,B] : m1_subset_1(k6_subset_1(A,B),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_subset_1)).

tff(c_54,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_10,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_50,plain,(
    r1_tarski(k2_relat_1('#skF_3'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_5247,plain,(
    ! [C_491,A_492,B_493] :
      ( m1_subset_1(C_491,k1_zfmisc_1(k2_zfmisc_1(A_492,B_493)))
      | ~ r1_tarski(k2_relat_1(C_491),B_493)
      | ~ r1_tarski(k1_relat_1(C_491),A_492)
      | ~ v1_relat_1(C_491) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_4,plain,(
    ! [A_1] :
      ( r2_hidden('#skF_1'(A_1),A_1)
      | k1_xboole_0 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_52,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_48,plain,
    ( ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2')))
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),'#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_56,plain,
    ( ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2')))
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_48])).

tff(c_88,plain,(
    ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_28,plain,(
    ! [A_13,B_14] :
      ( m1_subset_1(A_13,k1_zfmisc_1(B_14))
      | ~ r1_tarski(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_299,plain,(
    ! [C_57,B_58,A_59] :
      ( ~ v1_xboole_0(C_57)
      | ~ m1_subset_1(B_58,k1_zfmisc_1(C_57))
      | ~ r2_hidden(A_59,B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_345,plain,(
    ! [B_67,A_68,A_69] :
      ( ~ v1_xboole_0(B_67)
      | ~ r2_hidden(A_68,A_69)
      | ~ r1_tarski(A_69,B_67) ) ),
    inference(resolution,[status(thm)],[c_28,c_299])).

tff(c_349,plain,(
    ! [B_70,A_71] :
      ( ~ v1_xboole_0(B_70)
      | ~ r1_tarski(A_71,B_70)
      | k1_xboole_0 = A_71 ) ),
    inference(resolution,[status(thm)],[c_4,c_345])).

tff(c_369,plain,
    ( ~ v1_xboole_0('#skF_2')
    | k2_relat_1('#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_50,c_349])).

tff(c_377,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_369])).

tff(c_523,plain,(
    ! [C_90,A_91,B_92] :
      ( m1_subset_1(C_90,k1_zfmisc_1(k2_zfmisc_1(A_91,B_92)))
      | ~ r1_tarski(k2_relat_1(C_90),B_92)
      | ~ r1_tarski(k1_relat_1(C_90),A_91)
      | ~ v1_relat_1(C_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_26,plain,(
    ! [A_13,B_14] :
      ( r1_tarski(A_13,B_14)
      | ~ m1_subset_1(A_13,k1_zfmisc_1(B_14)) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_942,plain,(
    ! [C_136,A_137,B_138] :
      ( r1_tarski(C_136,k2_zfmisc_1(A_137,B_138))
      | ~ r1_tarski(k2_relat_1(C_136),B_138)
      | ~ r1_tarski(k1_relat_1(C_136),A_137)
      | ~ v1_relat_1(C_136) ) ),
    inference(resolution,[status(thm)],[c_523,c_26])).

tff(c_947,plain,(
    ! [A_137] :
      ( r1_tarski('#skF_3',k2_zfmisc_1(A_137,'#skF_2'))
      | ~ r1_tarski(k1_relat_1('#skF_3'),A_137)
      | ~ v1_relat_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_50,c_942])).

tff(c_956,plain,(
    ! [A_139] :
      ( r1_tarski('#skF_3',k2_zfmisc_1(A_139,'#skF_2'))
      | ~ r1_tarski(k1_relat_1('#skF_3'),A_139) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_947])).

tff(c_966,plain,(
    r1_tarski('#skF_3',k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2')) ),
    inference(resolution,[status(thm)],[c_10,c_956])).

tff(c_459,plain,(
    ! [A_81,B_82,C_83] :
      ( k1_relset_1(A_81,B_82,C_83) = k1_relat_1(C_83)
      | ~ m1_subset_1(C_83,k1_zfmisc_1(k2_zfmisc_1(A_81,B_82))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_479,plain,(
    ! [A_81,B_82,A_13] :
      ( k1_relset_1(A_81,B_82,A_13) = k1_relat_1(A_13)
      | ~ r1_tarski(A_13,k2_zfmisc_1(A_81,B_82)) ) ),
    inference(resolution,[status(thm)],[c_28,c_459])).

tff(c_981,plain,(
    k1_relset_1(k1_relat_1('#skF_3'),'#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_966,c_479])).

tff(c_806,plain,(
    ! [B_122,C_123,A_124] :
      ( k1_xboole_0 = B_122
      | v1_funct_2(C_123,A_124,B_122)
      | k1_relset_1(A_124,B_122,C_123) != A_124
      | ~ m1_subset_1(C_123,k1_zfmisc_1(k2_zfmisc_1(A_124,B_122))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_1378,plain,(
    ! [B_173,A_174,A_175] :
      ( k1_xboole_0 = B_173
      | v1_funct_2(A_174,A_175,B_173)
      | k1_relset_1(A_175,B_173,A_174) != A_175
      | ~ r1_tarski(A_174,k2_zfmisc_1(A_175,B_173)) ) ),
    inference(resolution,[status(thm)],[c_28,c_806])).

tff(c_1387,plain,
    ( k1_xboole_0 = '#skF_2'
    | v1_funct_2('#skF_3',k1_relat_1('#skF_3'),'#skF_2')
    | k1_relset_1(k1_relat_1('#skF_3'),'#skF_2','#skF_3') != k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_966,c_1378])).

tff(c_1414,plain,
    ( k1_xboole_0 = '#skF_2'
    | v1_funct_2('#skF_3',k1_relat_1('#skF_3'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_981,c_1387])).

tff(c_1415,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_1414])).

tff(c_1489,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1415,c_2])).

tff(c_1491,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_377,c_1489])).

tff(c_1493,plain,(
    v1_xboole_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_369])).

tff(c_370,plain,(
    ! [B_4] :
      ( ~ v1_xboole_0(B_4)
      | k1_xboole_0 = B_4 ) ),
    inference(resolution,[status(thm)],[c_10,c_349])).

tff(c_1499,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_1493,c_370])).

tff(c_1492,plain,(
    k2_relat_1('#skF_3') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_369])).

tff(c_1527,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1499,c_1492])).

tff(c_221,plain,(
    ! [B_51,A_52] :
      ( B_51 = A_52
      | ~ r1_tarski(B_51,A_52)
      | ~ r1_tarski(A_52,B_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_235,plain,
    ( k2_relat_1('#skF_3') = '#skF_2'
    | ~ r1_tarski('#skF_2',k2_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_50,c_221])).

tff(c_294,plain,(
    ~ r1_tarski('#skF_2',k2_relat_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_235])).

tff(c_1528,plain,(
    ~ r1_tarski('#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1527,c_294])).

tff(c_1532,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_1528])).

tff(c_1533,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_235])).

tff(c_1735,plain,(
    ! [C_209,A_210,B_211] :
      ( m1_subset_1(C_209,k1_zfmisc_1(k2_zfmisc_1(A_210,B_211)))
      | ~ r1_tarski(k2_relat_1(C_209),B_211)
      | ~ r1_tarski(k1_relat_1(C_209),A_210)
      | ~ v1_relat_1(C_209) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_3611,plain,(
    ! [C_367,A_368,B_369] :
      ( r1_tarski(C_367,k2_zfmisc_1(A_368,B_369))
      | ~ r1_tarski(k2_relat_1(C_367),B_369)
      | ~ r1_tarski(k1_relat_1(C_367),A_368)
      | ~ v1_relat_1(C_367) ) ),
    inference(resolution,[status(thm)],[c_1735,c_26])).

tff(c_3624,plain,(
    ! [C_370,A_371] :
      ( r1_tarski(C_370,k2_zfmisc_1(A_371,k2_relat_1(C_370)))
      | ~ r1_tarski(k1_relat_1(C_370),A_371)
      | ~ v1_relat_1(C_370) ) ),
    inference(resolution,[status(thm)],[c_10,c_3611])).

tff(c_3644,plain,(
    ! [A_371] :
      ( r1_tarski('#skF_3',k2_zfmisc_1(A_371,'#skF_2'))
      | ~ r1_tarski(k1_relat_1('#skF_3'),A_371)
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1533,c_3624])).

tff(c_3667,plain,(
    ! [A_373] :
      ( r1_tarski('#skF_3',k2_zfmisc_1(A_373,'#skF_2'))
      | ~ r1_tarski(k1_relat_1('#skF_3'),A_373) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_3644])).

tff(c_3682,plain,(
    r1_tarski('#skF_3',k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2')) ),
    inference(resolution,[status(thm)],[c_10,c_3667])).

tff(c_1591,plain,(
    ! [A_189,B_190,C_191] :
      ( k1_relset_1(A_189,B_190,C_191) = k1_relat_1(C_191)
      | ~ m1_subset_1(C_191,k1_zfmisc_1(k2_zfmisc_1(A_189,B_190))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_1611,plain,(
    ! [A_189,B_190,A_13] :
      ( k1_relset_1(A_189,B_190,A_13) = k1_relat_1(A_13)
      | ~ r1_tarski(A_13,k2_zfmisc_1(A_189,B_190)) ) ),
    inference(resolution,[status(thm)],[c_28,c_1591])).

tff(c_3710,plain,(
    k1_relset_1(k1_relat_1('#skF_3'),'#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_3682,c_1611])).

tff(c_3346,plain,(
    ! [B_338,C_339,A_340] :
      ( k1_xboole_0 = B_338
      | v1_funct_2(C_339,A_340,B_338)
      | k1_relset_1(A_340,B_338,C_339) != A_340
      | ~ m1_subset_1(C_339,k1_zfmisc_1(k2_zfmisc_1(A_340,B_338))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_3979,plain,(
    ! [B_387,A_388,A_389] :
      ( k1_xboole_0 = B_387
      | v1_funct_2(A_388,A_389,B_387)
      | k1_relset_1(A_389,B_387,A_388) != A_389
      | ~ r1_tarski(A_388,k2_zfmisc_1(A_389,B_387)) ) ),
    inference(resolution,[status(thm)],[c_28,c_3346])).

tff(c_3991,plain,
    ( k1_xboole_0 = '#skF_2'
    | v1_funct_2('#skF_3',k1_relat_1('#skF_3'),'#skF_2')
    | k1_relset_1(k1_relat_1('#skF_3'),'#skF_2','#skF_3') != k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_3682,c_3979])).

tff(c_4022,plain,
    ( k1_xboole_0 = '#skF_2'
    | v1_funct_2('#skF_3',k1_relat_1('#skF_3'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3710,c_3991])).

tff(c_4023,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_4022])).

tff(c_18,plain,(
    ! [A_7] : k2_zfmisc_1(A_7,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_3569,plain,(
    ! [C_357,A_358] :
      ( m1_subset_1(C_357,k1_zfmisc_1(k1_xboole_0))
      | ~ r1_tarski(k2_relat_1(C_357),k1_xboole_0)
      | ~ r1_tarski(k1_relat_1(C_357),A_358)
      | ~ v1_relat_1(C_357) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_1735])).

tff(c_3571,plain,(
    ! [A_358] :
      ( m1_subset_1('#skF_3',k1_zfmisc_1(k1_xboole_0))
      | ~ r1_tarski('#skF_2',k1_xboole_0)
      | ~ r1_tarski(k1_relat_1('#skF_3'),A_358)
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1533,c_3569])).

tff(c_3576,plain,(
    ! [A_358] :
      ( m1_subset_1('#skF_3',k1_zfmisc_1(k1_xboole_0))
      | ~ r1_tarski('#skF_2',k1_xboole_0)
      | ~ r1_tarski(k1_relat_1('#skF_3'),A_358) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_3571])).

tff(c_3595,plain,(
    ~ r1_tarski('#skF_2',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_3576])).

tff(c_4044,plain,(
    ~ r1_tarski('#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4023,c_3595])).

tff(c_4096,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_4044])).

tff(c_4098,plain,(
    r1_tarski('#skF_2',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_3576])).

tff(c_1544,plain,(
    ! [C_176,B_177,A_178] :
      ( ~ v1_xboole_0(C_176)
      | ~ m1_subset_1(B_177,k1_zfmisc_1(C_176))
      | ~ r2_hidden(A_178,B_177) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_1587,plain,(
    ! [B_186,A_187,A_188] :
      ( ~ v1_xboole_0(B_186)
      | ~ r2_hidden(A_187,A_188)
      | ~ r1_tarski(A_188,B_186) ) ),
    inference(resolution,[status(thm)],[c_28,c_1544])).

tff(c_1590,plain,(
    ! [B_186,A_1] :
      ( ~ v1_xboole_0(B_186)
      | ~ r1_tarski(A_1,B_186)
      | k1_xboole_0 = A_1 ) ),
    inference(resolution,[status(thm)],[c_4,c_1587])).

tff(c_4108,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_4098,c_1590])).

tff(c_4124,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_4108])).

tff(c_109,plain,(
    ! [A_41,B_42] :
      ( k4_xboole_0(A_41,B_42) = k1_xboole_0
      | ~ r1_tarski(A_41,B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_122,plain,(
    ! [B_43] : k4_xboole_0(B_43,B_43) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_10,c_109])).

tff(c_24,plain,(
    ! [A_11,B_12] : k6_subset_1(A_11,B_12) = k4_xboole_0(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_22,plain,(
    ! [A_9,B_10] : m1_subset_1(k6_subset_1(A_9,B_10),k1_zfmisc_1(A_9)) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_57,plain,(
    ! [A_9,B_10] : m1_subset_1(k4_xboole_0(A_9,B_10),k1_zfmisc_1(A_9)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22])).

tff(c_132,plain,(
    ! [B_44] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(B_44)) ),
    inference(superposition,[status(thm),theory(equality)],[c_122,c_57])).

tff(c_136,plain,(
    ! [B_44] : r1_tarski(k1_xboole_0,B_44) ),
    inference(resolution,[status(thm)],[c_132,c_26])).

tff(c_4171,plain,(
    ! [B_44] : r1_tarski('#skF_2',B_44) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4124,c_136])).

tff(c_4097,plain,(
    ! [A_358] :
      ( ~ r1_tarski(k1_relat_1('#skF_3'),A_358)
      | m1_subset_1('#skF_3',k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(splitRight,[status(thm)],[c_3576])).

tff(c_4185,plain,(
    ! [A_358] :
      ( ~ r1_tarski(k1_relat_1('#skF_3'),A_358)
      | m1_subset_1('#skF_3',k1_zfmisc_1('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4124,c_4097])).

tff(c_4253,plain,(
    ! [A_398] : ~ r1_tarski(k1_relat_1('#skF_3'),A_398) ),
    inference(splitLeft,[status(thm)],[c_4185])).

tff(c_4258,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_10,c_4253])).

tff(c_4259,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_4185])).

tff(c_4428,plain,(
    r1_tarski('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_4259,c_26])).

tff(c_6,plain,(
    ! [B_4,A_3] :
      ( B_4 = A_3
      | ~ r1_tarski(B_4,A_3)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_4435,plain,
    ( '#skF_2' = '#skF_3'
    | ~ r1_tarski('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_4428,c_6])).

tff(c_4438,plain,(
    '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4171,c_4435])).

tff(c_2206,plain,(
    ! [C_265,A_266,B_267] :
      ( r1_tarski(C_265,k2_zfmisc_1(A_266,B_267))
      | ~ r1_tarski(k2_relat_1(C_265),B_267)
      | ~ r1_tarski(k1_relat_1(C_265),A_266)
      | ~ v1_relat_1(C_265) ) ),
    inference(resolution,[status(thm)],[c_1735,c_26])).

tff(c_2331,plain,(
    ! [C_277,A_278] :
      ( r1_tarski(C_277,k2_zfmisc_1(A_278,k2_relat_1(C_277)))
      | ~ r1_tarski(k1_relat_1(C_277),A_278)
      | ~ v1_relat_1(C_277) ) ),
    inference(resolution,[status(thm)],[c_10,c_2206])).

tff(c_2357,plain,(
    ! [A_278] :
      ( r1_tarski('#skF_3',k2_zfmisc_1(A_278,'#skF_2'))
      | ~ r1_tarski(k1_relat_1('#skF_3'),A_278)
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1533,c_2331])).

tff(c_2377,plain,(
    ! [A_280] :
      ( r1_tarski('#skF_3',k2_zfmisc_1(A_280,'#skF_2'))
      | ~ r1_tarski(k1_relat_1('#skF_3'),A_280) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_2357])).

tff(c_2392,plain,(
    r1_tarski('#skF_3',k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2')) ),
    inference(resolution,[status(thm)],[c_10,c_2377])).

tff(c_2420,plain,(
    k1_relset_1(k1_relat_1('#skF_3'),'#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_2392,c_1611])).

tff(c_2028,plain,(
    ! [B_241,C_242,A_243] :
      ( k1_xboole_0 = B_241
      | v1_funct_2(C_242,A_243,B_241)
      | k1_relset_1(A_243,B_241,C_242) != A_243
      | ~ m1_subset_1(C_242,k1_zfmisc_1(k2_zfmisc_1(A_243,B_241))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_2621,plain,(
    ! [B_291,A_292,A_293] :
      ( k1_xboole_0 = B_291
      | v1_funct_2(A_292,A_293,B_291)
      | k1_relset_1(A_293,B_291,A_292) != A_293
      | ~ r1_tarski(A_292,k2_zfmisc_1(A_293,B_291)) ) ),
    inference(resolution,[status(thm)],[c_28,c_2028])).

tff(c_2630,plain,
    ( k1_xboole_0 = '#skF_2'
    | v1_funct_2('#skF_3',k1_relat_1('#skF_3'),'#skF_2')
    | k1_relset_1(k1_relat_1('#skF_3'),'#skF_2','#skF_3') != k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_2392,c_2621])).

tff(c_2663,plain,
    ( k1_xboole_0 = '#skF_2'
    | v1_funct_2('#skF_3',k1_relat_1('#skF_3'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2420,c_2630])).

tff(c_2664,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_2663])).

tff(c_2117,plain,(
    ! [C_251,A_252] :
      ( m1_subset_1(C_251,k1_zfmisc_1(k1_xboole_0))
      | ~ r1_tarski(k2_relat_1(C_251),k1_xboole_0)
      | ~ r1_tarski(k1_relat_1(C_251),A_252)
      | ~ v1_relat_1(C_251) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_1735])).

tff(c_2119,plain,(
    ! [A_252] :
      ( m1_subset_1('#skF_3',k1_zfmisc_1(k1_xboole_0))
      | ~ r1_tarski('#skF_2',k1_xboole_0)
      | ~ r1_tarski(k1_relat_1('#skF_3'),A_252)
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1533,c_2117])).

tff(c_2124,plain,(
    ! [A_252] :
      ( m1_subset_1('#skF_3',k1_zfmisc_1(k1_xboole_0))
      | ~ r1_tarski('#skF_2',k1_xboole_0)
      | ~ r1_tarski(k1_relat_1('#skF_3'),A_252) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_2119])).

tff(c_2126,plain,(
    ~ r1_tarski('#skF_2',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_2124])).

tff(c_2691,plain,(
    ~ r1_tarski('#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2664,c_2126])).

tff(c_2738,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_2691])).

tff(c_2740,plain,(
    r1_tarski('#skF_2',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_2124])).

tff(c_2750,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_2740,c_1590])).

tff(c_2766,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_2750])).

tff(c_2808,plain,(
    ! [B_44] : r1_tarski('#skF_2',B_44) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2766,c_136])).

tff(c_2739,plain,(
    ! [A_252] :
      ( ~ r1_tarski(k1_relat_1('#skF_3'),A_252)
      | m1_subset_1('#skF_3',k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(splitRight,[status(thm)],[c_2124])).

tff(c_2822,plain,(
    ! [A_252] :
      ( ~ r1_tarski(k1_relat_1('#skF_3'),A_252)
      | m1_subset_1('#skF_3',k1_zfmisc_1('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2766,c_2739])).

tff(c_2851,plain,(
    ! [A_299] : ~ r1_tarski(k1_relat_1('#skF_3'),A_299) ),
    inference(splitLeft,[status(thm)],[c_2822])).

tff(c_2856,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_10,c_2851])).

tff(c_2857,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_2822])).

tff(c_2976,plain,(
    r1_tarski('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_2857,c_26])).

tff(c_2979,plain,
    ( '#skF_2' = '#skF_3'
    | ~ r1_tarski('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_2976,c_6])).

tff(c_2982,plain,(
    '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2808,c_2979])).

tff(c_127,plain,(
    ! [B_43] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(B_43)) ),
    inference(superposition,[status(thm),theory(equality)],[c_122,c_57])).

tff(c_1610,plain,(
    ! [A_189,B_190] : k1_relset_1(A_189,B_190,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_127,c_1591])).

tff(c_20,plain,(
    ! [B_8] : k2_zfmisc_1(k1_xboole_0,B_8) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_40,plain,(
    ! [C_26,B_25] :
      ( v1_funct_2(C_26,k1_xboole_0,B_25)
      | k1_relset_1(k1_xboole_0,B_25,C_26) != k1_xboole_0
      | ~ m1_subset_1(C_26,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_25))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_2012,plain,(
    ! [C_239,B_240] :
      ( v1_funct_2(C_239,k1_xboole_0,B_240)
      | k1_relset_1(k1_xboole_0,B_240,C_239) != k1_xboole_0
      | ~ m1_subset_1(C_239,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_40])).

tff(c_2015,plain,(
    ! [B_240] :
      ( v1_funct_2(k1_xboole_0,k1_xboole_0,B_240)
      | k1_relset_1(k1_xboole_0,B_240,k1_xboole_0) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_127,c_2012])).

tff(c_2023,plain,(
    ! [B_240] :
      ( v1_funct_2(k1_xboole_0,k1_xboole_0,B_240)
      | k1_relat_1(k1_xboole_0) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1610,c_2015])).

tff(c_2027,plain,(
    k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_2023])).

tff(c_2779,plain,(
    k1_relat_1('#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2766,c_2766,c_2027])).

tff(c_2988,plain,(
    k1_relat_1('#skF_3') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2982,c_2982,c_2779])).

tff(c_36,plain,(
    ! [A_24] :
      ( v1_funct_2(k1_xboole_0,A_24,k1_xboole_0)
      | k1_xboole_0 = A_24
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(A_24,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_60,plain,(
    ! [A_24] :
      ( v1_funct_2(k1_xboole_0,A_24,k1_xboole_0)
      | k1_xboole_0 = A_24
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_36])).

tff(c_1563,plain,(
    ! [A_24] :
      ( v1_funct_2(k1_xboole_0,A_24,k1_xboole_0)
      | k1_xboole_0 = A_24 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_60])).

tff(c_2801,plain,(
    ! [A_24] :
      ( v1_funct_2('#skF_2',A_24,'#skF_2')
      | A_24 = '#skF_2' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2766,c_2766,c_2766,c_1563])).

tff(c_3336,plain,(
    ! [A_337] :
      ( v1_funct_2('#skF_3',A_337,'#skF_3')
      | A_337 = '#skF_3' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2982,c_2982,c_2982,c_2801])).

tff(c_2994,plain,(
    ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2982,c_88])).

tff(c_3339,plain,(
    k1_relat_1('#skF_3') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_3336,c_2994])).

tff(c_3343,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2988,c_3339])).

tff(c_3345,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_2023])).

tff(c_4144,plain,(
    k1_relat_1('#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4124,c_4124,c_3345])).

tff(c_4448,plain,(
    k1_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4438,c_4438,c_4144])).

tff(c_3520,plain,(
    ! [C_353,B_354] :
      ( m1_subset_1(C_353,k1_zfmisc_1(k1_xboole_0))
      | ~ r1_tarski(k2_relat_1(C_353),B_354)
      | ~ r1_tarski(k1_relat_1(C_353),k1_xboole_0)
      | ~ v1_relat_1(C_353) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_1735])).

tff(c_3523,plain,(
    ! [B_354] :
      ( m1_subset_1('#skF_3',k1_zfmisc_1(k1_xboole_0))
      | ~ r1_tarski('#skF_2',B_354)
      | ~ r1_tarski(k1_relat_1('#skF_3'),k1_xboole_0)
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1533,c_3520])).

tff(c_3532,plain,(
    ! [B_354] :
      ( m1_subset_1('#skF_3',k1_zfmisc_1(k1_xboole_0))
      | ~ r1_tarski('#skF_2',B_354)
      | ~ r1_tarski(k1_relat_1('#skF_3'),k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_3523])).

tff(c_3545,plain,(
    ~ r1_tarski(k1_relat_1('#skF_3'),k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_3532])).

tff(c_4137,plain,(
    ~ r1_tarski(k1_relat_1('#skF_3'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4124,c_3545])).

tff(c_4534,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_4448,c_4438,c_4137])).

tff(c_4536,plain,(
    r1_tarski(k1_relat_1('#skF_3'),k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_3532])).

tff(c_3534,plain,(
    ! [C_353] :
      ( m1_subset_1(C_353,k1_zfmisc_1(k1_xboole_0))
      | ~ r1_tarski(k1_relat_1(C_353),k1_xboole_0)
      | ~ v1_relat_1(C_353) ) ),
    inference(resolution,[status(thm)],[c_10,c_3520])).

tff(c_4539,plain,
    ( m1_subset_1('#skF_3',k1_zfmisc_1(k1_xboole_0))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_4536,c_3534])).

tff(c_4560,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_4539])).

tff(c_30,plain,(
    ! [C_17,B_16,A_15] :
      ( ~ v1_xboole_0(C_17)
      | ~ m1_subset_1(B_16,k1_zfmisc_1(C_17))
      | ~ r2_hidden(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_4609,plain,(
    ! [A_15] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ r2_hidden(A_15,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_4560,c_30])).

tff(c_4622,plain,(
    ! [A_424] : ~ r2_hidden(A_424,'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_4609])).

tff(c_4627,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_4,c_4622])).

tff(c_3344,plain,(
    ! [B_240] : v1_funct_2(k1_xboole_0,k1_xboole_0,B_240) ),
    inference(splitRight,[status(thm)],[c_2023])).

tff(c_4637,plain,(
    ! [B_240] : v1_funct_2('#skF_3','#skF_3',B_240) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4627,c_4627,c_3344])).

tff(c_4549,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | k1_relat_1('#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_4536,c_1590])).

tff(c_4568,plain,(
    k1_relat_1('#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_4549])).

tff(c_4575,plain,(
    ~ v1_funct_2('#skF_3',k1_xboole_0,'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4568,c_88])).

tff(c_4629,plain,(
    ~ v1_funct_2('#skF_3','#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4627,c_4575])).

tff(c_4821,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4637,c_4629])).

tff(c_4822,plain,(
    ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_5258,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_3'),'#skF_2')
    | ~ r1_tarski(k1_relat_1('#skF_3'),k1_relat_1('#skF_3'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_5247,c_4822])).

tff(c_5271,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_10,c_50,c_5258])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 11:47:37 EST 2020
% 0.19/0.35  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.76/2.14  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.76/2.16  
% 5.76/2.16  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.76/2.17  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k6_subset_1 > k4_xboole_0 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3
% 5.76/2.17  
% 5.76/2.17  %Foreground sorts:
% 5.76/2.17  
% 5.76/2.17  
% 5.76/2.17  %Background operators:
% 5.76/2.17  
% 5.76/2.17  
% 5.76/2.17  %Foreground operators:
% 5.76/2.17  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.76/2.17  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.76/2.17  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.76/2.17  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.76/2.17  tff('#skF_1', type, '#skF_1': $i > $i).
% 5.76/2.17  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.76/2.17  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.76/2.17  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.76/2.17  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.76/2.17  tff('#skF_2', type, '#skF_2': $i).
% 5.76/2.17  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 5.76/2.17  tff('#skF_3', type, '#skF_3': $i).
% 5.76/2.17  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 5.76/2.17  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.76/2.17  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.76/2.17  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.76/2.17  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.76/2.17  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.76/2.17  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.76/2.17  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.76/2.17  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.76/2.17  
% 5.76/2.20  tff(f_108, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(k2_relat_1(B), A) => ((v1_funct_1(B) & v1_funct_2(B, k1_relat_1(B), A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B), A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_funct_2)).
% 5.76/2.20  tff(f_40, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.76/2.20  tff(f_77, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_relset_1)).
% 5.76/2.20  tff(f_34, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 5.76/2.20  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 5.76/2.20  tff(f_58, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 5.76/2.20  tff(f_65, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 5.76/2.20  tff(f_69, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 5.76/2.20  tff(f_95, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 5.76/2.20  tff(f_50, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 5.76/2.20  tff(f_44, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 5.76/2.20  tff(f_54, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 5.76/2.20  tff(f_52, axiom, (![A, B]: m1_subset_1(k6_subset_1(A, B), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_subset_1)).
% 5.76/2.20  tff(c_54, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_108])).
% 5.76/2.20  tff(c_10, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_40])).
% 5.76/2.20  tff(c_50, plain, (r1_tarski(k2_relat_1('#skF_3'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_108])).
% 5.76/2.20  tff(c_5247, plain, (![C_491, A_492, B_493]: (m1_subset_1(C_491, k1_zfmisc_1(k2_zfmisc_1(A_492, B_493))) | ~r1_tarski(k2_relat_1(C_491), B_493) | ~r1_tarski(k1_relat_1(C_491), A_492) | ~v1_relat_1(C_491))), inference(cnfTransformation, [status(thm)], [f_77])).
% 5.76/2.20  tff(c_4, plain, (![A_1]: (r2_hidden('#skF_1'(A_1), A_1) | k1_xboole_0=A_1)), inference(cnfTransformation, [status(thm)], [f_34])).
% 5.76/2.20  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 5.76/2.20  tff(c_52, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_108])).
% 5.76/2.20  tff(c_48, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2'))) | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), '#skF_2') | ~v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_108])).
% 5.76/2.20  tff(c_56, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2'))) | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_48])).
% 5.76/2.20  tff(c_88, plain, (~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), '#skF_2')), inference(splitLeft, [status(thm)], [c_56])).
% 5.76/2.20  tff(c_28, plain, (![A_13, B_14]: (m1_subset_1(A_13, k1_zfmisc_1(B_14)) | ~r1_tarski(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_58])).
% 5.76/2.20  tff(c_299, plain, (![C_57, B_58, A_59]: (~v1_xboole_0(C_57) | ~m1_subset_1(B_58, k1_zfmisc_1(C_57)) | ~r2_hidden(A_59, B_58))), inference(cnfTransformation, [status(thm)], [f_65])).
% 5.76/2.20  tff(c_345, plain, (![B_67, A_68, A_69]: (~v1_xboole_0(B_67) | ~r2_hidden(A_68, A_69) | ~r1_tarski(A_69, B_67))), inference(resolution, [status(thm)], [c_28, c_299])).
% 5.76/2.20  tff(c_349, plain, (![B_70, A_71]: (~v1_xboole_0(B_70) | ~r1_tarski(A_71, B_70) | k1_xboole_0=A_71)), inference(resolution, [status(thm)], [c_4, c_345])).
% 5.76/2.20  tff(c_369, plain, (~v1_xboole_0('#skF_2') | k2_relat_1('#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_50, c_349])).
% 5.76/2.20  tff(c_377, plain, (~v1_xboole_0('#skF_2')), inference(splitLeft, [status(thm)], [c_369])).
% 5.76/2.20  tff(c_523, plain, (![C_90, A_91, B_92]: (m1_subset_1(C_90, k1_zfmisc_1(k2_zfmisc_1(A_91, B_92))) | ~r1_tarski(k2_relat_1(C_90), B_92) | ~r1_tarski(k1_relat_1(C_90), A_91) | ~v1_relat_1(C_90))), inference(cnfTransformation, [status(thm)], [f_77])).
% 5.76/2.20  tff(c_26, plain, (![A_13, B_14]: (r1_tarski(A_13, B_14) | ~m1_subset_1(A_13, k1_zfmisc_1(B_14)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 5.76/2.20  tff(c_942, plain, (![C_136, A_137, B_138]: (r1_tarski(C_136, k2_zfmisc_1(A_137, B_138)) | ~r1_tarski(k2_relat_1(C_136), B_138) | ~r1_tarski(k1_relat_1(C_136), A_137) | ~v1_relat_1(C_136))), inference(resolution, [status(thm)], [c_523, c_26])).
% 5.76/2.20  tff(c_947, plain, (![A_137]: (r1_tarski('#skF_3', k2_zfmisc_1(A_137, '#skF_2')) | ~r1_tarski(k1_relat_1('#skF_3'), A_137) | ~v1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_50, c_942])).
% 5.76/2.20  tff(c_956, plain, (![A_139]: (r1_tarski('#skF_3', k2_zfmisc_1(A_139, '#skF_2')) | ~r1_tarski(k1_relat_1('#skF_3'), A_139))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_947])).
% 5.76/2.20  tff(c_966, plain, (r1_tarski('#skF_3', k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2'))), inference(resolution, [status(thm)], [c_10, c_956])).
% 5.76/2.20  tff(c_459, plain, (![A_81, B_82, C_83]: (k1_relset_1(A_81, B_82, C_83)=k1_relat_1(C_83) | ~m1_subset_1(C_83, k1_zfmisc_1(k2_zfmisc_1(A_81, B_82))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 5.76/2.20  tff(c_479, plain, (![A_81, B_82, A_13]: (k1_relset_1(A_81, B_82, A_13)=k1_relat_1(A_13) | ~r1_tarski(A_13, k2_zfmisc_1(A_81, B_82)))), inference(resolution, [status(thm)], [c_28, c_459])).
% 5.76/2.20  tff(c_981, plain, (k1_relset_1(k1_relat_1('#skF_3'), '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_966, c_479])).
% 5.76/2.20  tff(c_806, plain, (![B_122, C_123, A_124]: (k1_xboole_0=B_122 | v1_funct_2(C_123, A_124, B_122) | k1_relset_1(A_124, B_122, C_123)!=A_124 | ~m1_subset_1(C_123, k1_zfmisc_1(k2_zfmisc_1(A_124, B_122))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 5.76/2.20  tff(c_1378, plain, (![B_173, A_174, A_175]: (k1_xboole_0=B_173 | v1_funct_2(A_174, A_175, B_173) | k1_relset_1(A_175, B_173, A_174)!=A_175 | ~r1_tarski(A_174, k2_zfmisc_1(A_175, B_173)))), inference(resolution, [status(thm)], [c_28, c_806])).
% 5.76/2.20  tff(c_1387, plain, (k1_xboole_0='#skF_2' | v1_funct_2('#skF_3', k1_relat_1('#skF_3'), '#skF_2') | k1_relset_1(k1_relat_1('#skF_3'), '#skF_2', '#skF_3')!=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_966, c_1378])).
% 5.76/2.20  tff(c_1414, plain, (k1_xboole_0='#skF_2' | v1_funct_2('#skF_3', k1_relat_1('#skF_3'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_981, c_1387])).
% 5.76/2.20  tff(c_1415, plain, (k1_xboole_0='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_88, c_1414])).
% 5.76/2.20  tff(c_1489, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1415, c_2])).
% 5.76/2.20  tff(c_1491, plain, $false, inference(negUnitSimplification, [status(thm)], [c_377, c_1489])).
% 5.76/2.20  tff(c_1493, plain, (v1_xboole_0('#skF_2')), inference(splitRight, [status(thm)], [c_369])).
% 5.76/2.20  tff(c_370, plain, (![B_4]: (~v1_xboole_0(B_4) | k1_xboole_0=B_4)), inference(resolution, [status(thm)], [c_10, c_349])).
% 5.76/2.20  tff(c_1499, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_1493, c_370])).
% 5.76/2.20  tff(c_1492, plain, (k2_relat_1('#skF_3')=k1_xboole_0), inference(splitRight, [status(thm)], [c_369])).
% 5.76/2.20  tff(c_1527, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_1499, c_1492])).
% 5.76/2.20  tff(c_221, plain, (![B_51, A_52]: (B_51=A_52 | ~r1_tarski(B_51, A_52) | ~r1_tarski(A_52, B_51))), inference(cnfTransformation, [status(thm)], [f_40])).
% 5.76/2.20  tff(c_235, plain, (k2_relat_1('#skF_3')='#skF_2' | ~r1_tarski('#skF_2', k2_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_50, c_221])).
% 5.76/2.20  tff(c_294, plain, (~r1_tarski('#skF_2', k2_relat_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_235])).
% 5.76/2.20  tff(c_1528, plain, (~r1_tarski('#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1527, c_294])).
% 5.76/2.20  tff(c_1532, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10, c_1528])).
% 5.76/2.20  tff(c_1533, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(splitRight, [status(thm)], [c_235])).
% 5.76/2.20  tff(c_1735, plain, (![C_209, A_210, B_211]: (m1_subset_1(C_209, k1_zfmisc_1(k2_zfmisc_1(A_210, B_211))) | ~r1_tarski(k2_relat_1(C_209), B_211) | ~r1_tarski(k1_relat_1(C_209), A_210) | ~v1_relat_1(C_209))), inference(cnfTransformation, [status(thm)], [f_77])).
% 5.76/2.20  tff(c_3611, plain, (![C_367, A_368, B_369]: (r1_tarski(C_367, k2_zfmisc_1(A_368, B_369)) | ~r1_tarski(k2_relat_1(C_367), B_369) | ~r1_tarski(k1_relat_1(C_367), A_368) | ~v1_relat_1(C_367))), inference(resolution, [status(thm)], [c_1735, c_26])).
% 5.76/2.20  tff(c_3624, plain, (![C_370, A_371]: (r1_tarski(C_370, k2_zfmisc_1(A_371, k2_relat_1(C_370))) | ~r1_tarski(k1_relat_1(C_370), A_371) | ~v1_relat_1(C_370))), inference(resolution, [status(thm)], [c_10, c_3611])).
% 5.76/2.20  tff(c_3644, plain, (![A_371]: (r1_tarski('#skF_3', k2_zfmisc_1(A_371, '#skF_2')) | ~r1_tarski(k1_relat_1('#skF_3'), A_371) | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1533, c_3624])).
% 5.76/2.20  tff(c_3667, plain, (![A_373]: (r1_tarski('#skF_3', k2_zfmisc_1(A_373, '#skF_2')) | ~r1_tarski(k1_relat_1('#skF_3'), A_373))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_3644])).
% 5.76/2.20  tff(c_3682, plain, (r1_tarski('#skF_3', k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2'))), inference(resolution, [status(thm)], [c_10, c_3667])).
% 5.76/2.20  tff(c_1591, plain, (![A_189, B_190, C_191]: (k1_relset_1(A_189, B_190, C_191)=k1_relat_1(C_191) | ~m1_subset_1(C_191, k1_zfmisc_1(k2_zfmisc_1(A_189, B_190))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 5.76/2.20  tff(c_1611, plain, (![A_189, B_190, A_13]: (k1_relset_1(A_189, B_190, A_13)=k1_relat_1(A_13) | ~r1_tarski(A_13, k2_zfmisc_1(A_189, B_190)))), inference(resolution, [status(thm)], [c_28, c_1591])).
% 5.76/2.20  tff(c_3710, plain, (k1_relset_1(k1_relat_1('#skF_3'), '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_3682, c_1611])).
% 5.76/2.20  tff(c_3346, plain, (![B_338, C_339, A_340]: (k1_xboole_0=B_338 | v1_funct_2(C_339, A_340, B_338) | k1_relset_1(A_340, B_338, C_339)!=A_340 | ~m1_subset_1(C_339, k1_zfmisc_1(k2_zfmisc_1(A_340, B_338))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 5.76/2.20  tff(c_3979, plain, (![B_387, A_388, A_389]: (k1_xboole_0=B_387 | v1_funct_2(A_388, A_389, B_387) | k1_relset_1(A_389, B_387, A_388)!=A_389 | ~r1_tarski(A_388, k2_zfmisc_1(A_389, B_387)))), inference(resolution, [status(thm)], [c_28, c_3346])).
% 5.76/2.20  tff(c_3991, plain, (k1_xboole_0='#skF_2' | v1_funct_2('#skF_3', k1_relat_1('#skF_3'), '#skF_2') | k1_relset_1(k1_relat_1('#skF_3'), '#skF_2', '#skF_3')!=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_3682, c_3979])).
% 5.76/2.20  tff(c_4022, plain, (k1_xboole_0='#skF_2' | v1_funct_2('#skF_3', k1_relat_1('#skF_3'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_3710, c_3991])).
% 5.76/2.20  tff(c_4023, plain, (k1_xboole_0='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_88, c_4022])).
% 5.76/2.20  tff(c_18, plain, (![A_7]: (k2_zfmisc_1(A_7, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_50])).
% 5.76/2.20  tff(c_3569, plain, (![C_357, A_358]: (m1_subset_1(C_357, k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski(k2_relat_1(C_357), k1_xboole_0) | ~r1_tarski(k1_relat_1(C_357), A_358) | ~v1_relat_1(C_357))), inference(superposition, [status(thm), theory('equality')], [c_18, c_1735])).
% 5.76/2.20  tff(c_3571, plain, (![A_358]: (m1_subset_1('#skF_3', k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski('#skF_2', k1_xboole_0) | ~r1_tarski(k1_relat_1('#skF_3'), A_358) | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1533, c_3569])).
% 5.76/2.20  tff(c_3576, plain, (![A_358]: (m1_subset_1('#skF_3', k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski('#skF_2', k1_xboole_0) | ~r1_tarski(k1_relat_1('#skF_3'), A_358))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_3571])).
% 5.76/2.20  tff(c_3595, plain, (~r1_tarski('#skF_2', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_3576])).
% 5.76/2.20  tff(c_4044, plain, (~r1_tarski('#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4023, c_3595])).
% 5.76/2.20  tff(c_4096, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10, c_4044])).
% 5.76/2.20  tff(c_4098, plain, (r1_tarski('#skF_2', k1_xboole_0)), inference(splitRight, [status(thm)], [c_3576])).
% 5.76/2.20  tff(c_1544, plain, (![C_176, B_177, A_178]: (~v1_xboole_0(C_176) | ~m1_subset_1(B_177, k1_zfmisc_1(C_176)) | ~r2_hidden(A_178, B_177))), inference(cnfTransformation, [status(thm)], [f_65])).
% 5.76/2.20  tff(c_1587, plain, (![B_186, A_187, A_188]: (~v1_xboole_0(B_186) | ~r2_hidden(A_187, A_188) | ~r1_tarski(A_188, B_186))), inference(resolution, [status(thm)], [c_28, c_1544])).
% 5.76/2.20  tff(c_1590, plain, (![B_186, A_1]: (~v1_xboole_0(B_186) | ~r1_tarski(A_1, B_186) | k1_xboole_0=A_1)), inference(resolution, [status(thm)], [c_4, c_1587])).
% 5.76/2.20  tff(c_4108, plain, (~v1_xboole_0(k1_xboole_0) | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_4098, c_1590])).
% 5.76/2.20  tff(c_4124, plain, (k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_2, c_4108])).
% 5.76/2.20  tff(c_109, plain, (![A_41, B_42]: (k4_xboole_0(A_41, B_42)=k1_xboole_0 | ~r1_tarski(A_41, B_42))), inference(cnfTransformation, [status(thm)], [f_44])).
% 5.76/2.20  tff(c_122, plain, (![B_43]: (k4_xboole_0(B_43, B_43)=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_109])).
% 5.76/2.20  tff(c_24, plain, (![A_11, B_12]: (k6_subset_1(A_11, B_12)=k4_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_54])).
% 5.76/2.20  tff(c_22, plain, (![A_9, B_10]: (m1_subset_1(k6_subset_1(A_9, B_10), k1_zfmisc_1(A_9)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 5.76/2.20  tff(c_57, plain, (![A_9, B_10]: (m1_subset_1(k4_xboole_0(A_9, B_10), k1_zfmisc_1(A_9)))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_22])).
% 5.76/2.20  tff(c_132, plain, (![B_44]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(B_44)))), inference(superposition, [status(thm), theory('equality')], [c_122, c_57])).
% 5.76/2.20  tff(c_136, plain, (![B_44]: (r1_tarski(k1_xboole_0, B_44))), inference(resolution, [status(thm)], [c_132, c_26])).
% 5.76/2.20  tff(c_4171, plain, (![B_44]: (r1_tarski('#skF_2', B_44))), inference(demodulation, [status(thm), theory('equality')], [c_4124, c_136])).
% 5.76/2.20  tff(c_4097, plain, (![A_358]: (~r1_tarski(k1_relat_1('#skF_3'), A_358) | m1_subset_1('#skF_3', k1_zfmisc_1(k1_xboole_0)))), inference(splitRight, [status(thm)], [c_3576])).
% 5.76/2.20  tff(c_4185, plain, (![A_358]: (~r1_tarski(k1_relat_1('#skF_3'), A_358) | m1_subset_1('#skF_3', k1_zfmisc_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_4124, c_4097])).
% 5.76/2.20  tff(c_4253, plain, (![A_398]: (~r1_tarski(k1_relat_1('#skF_3'), A_398))), inference(splitLeft, [status(thm)], [c_4185])).
% 5.76/2.20  tff(c_4258, plain, $false, inference(resolution, [status(thm)], [c_10, c_4253])).
% 5.76/2.20  tff(c_4259, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_2'))), inference(splitRight, [status(thm)], [c_4185])).
% 5.76/2.20  tff(c_4428, plain, (r1_tarski('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_4259, c_26])).
% 5.76/2.20  tff(c_6, plain, (![B_4, A_3]: (B_4=A_3 | ~r1_tarski(B_4, A_3) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_40])).
% 5.76/2.20  tff(c_4435, plain, ('#skF_2'='#skF_3' | ~r1_tarski('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_4428, c_6])).
% 5.76/2.20  tff(c_4438, plain, ('#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_4171, c_4435])).
% 5.76/2.20  tff(c_2206, plain, (![C_265, A_266, B_267]: (r1_tarski(C_265, k2_zfmisc_1(A_266, B_267)) | ~r1_tarski(k2_relat_1(C_265), B_267) | ~r1_tarski(k1_relat_1(C_265), A_266) | ~v1_relat_1(C_265))), inference(resolution, [status(thm)], [c_1735, c_26])).
% 5.76/2.20  tff(c_2331, plain, (![C_277, A_278]: (r1_tarski(C_277, k2_zfmisc_1(A_278, k2_relat_1(C_277))) | ~r1_tarski(k1_relat_1(C_277), A_278) | ~v1_relat_1(C_277))), inference(resolution, [status(thm)], [c_10, c_2206])).
% 5.76/2.20  tff(c_2357, plain, (![A_278]: (r1_tarski('#skF_3', k2_zfmisc_1(A_278, '#skF_2')) | ~r1_tarski(k1_relat_1('#skF_3'), A_278) | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1533, c_2331])).
% 5.76/2.20  tff(c_2377, plain, (![A_280]: (r1_tarski('#skF_3', k2_zfmisc_1(A_280, '#skF_2')) | ~r1_tarski(k1_relat_1('#skF_3'), A_280))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_2357])).
% 5.76/2.20  tff(c_2392, plain, (r1_tarski('#skF_3', k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2'))), inference(resolution, [status(thm)], [c_10, c_2377])).
% 5.76/2.20  tff(c_2420, plain, (k1_relset_1(k1_relat_1('#skF_3'), '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_2392, c_1611])).
% 5.76/2.20  tff(c_2028, plain, (![B_241, C_242, A_243]: (k1_xboole_0=B_241 | v1_funct_2(C_242, A_243, B_241) | k1_relset_1(A_243, B_241, C_242)!=A_243 | ~m1_subset_1(C_242, k1_zfmisc_1(k2_zfmisc_1(A_243, B_241))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 5.76/2.20  tff(c_2621, plain, (![B_291, A_292, A_293]: (k1_xboole_0=B_291 | v1_funct_2(A_292, A_293, B_291) | k1_relset_1(A_293, B_291, A_292)!=A_293 | ~r1_tarski(A_292, k2_zfmisc_1(A_293, B_291)))), inference(resolution, [status(thm)], [c_28, c_2028])).
% 5.76/2.20  tff(c_2630, plain, (k1_xboole_0='#skF_2' | v1_funct_2('#skF_3', k1_relat_1('#skF_3'), '#skF_2') | k1_relset_1(k1_relat_1('#skF_3'), '#skF_2', '#skF_3')!=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_2392, c_2621])).
% 5.76/2.20  tff(c_2663, plain, (k1_xboole_0='#skF_2' | v1_funct_2('#skF_3', k1_relat_1('#skF_3'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2420, c_2630])).
% 5.76/2.20  tff(c_2664, plain, (k1_xboole_0='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_88, c_2663])).
% 5.76/2.20  tff(c_2117, plain, (![C_251, A_252]: (m1_subset_1(C_251, k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski(k2_relat_1(C_251), k1_xboole_0) | ~r1_tarski(k1_relat_1(C_251), A_252) | ~v1_relat_1(C_251))), inference(superposition, [status(thm), theory('equality')], [c_18, c_1735])).
% 5.76/2.20  tff(c_2119, plain, (![A_252]: (m1_subset_1('#skF_3', k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski('#skF_2', k1_xboole_0) | ~r1_tarski(k1_relat_1('#skF_3'), A_252) | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1533, c_2117])).
% 5.76/2.20  tff(c_2124, plain, (![A_252]: (m1_subset_1('#skF_3', k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski('#skF_2', k1_xboole_0) | ~r1_tarski(k1_relat_1('#skF_3'), A_252))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_2119])).
% 5.76/2.20  tff(c_2126, plain, (~r1_tarski('#skF_2', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_2124])).
% 5.76/2.20  tff(c_2691, plain, (~r1_tarski('#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2664, c_2126])).
% 5.76/2.20  tff(c_2738, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10, c_2691])).
% 5.76/2.20  tff(c_2740, plain, (r1_tarski('#skF_2', k1_xboole_0)), inference(splitRight, [status(thm)], [c_2124])).
% 5.76/2.20  tff(c_2750, plain, (~v1_xboole_0(k1_xboole_0) | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_2740, c_1590])).
% 5.76/2.20  tff(c_2766, plain, (k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_2, c_2750])).
% 5.76/2.20  tff(c_2808, plain, (![B_44]: (r1_tarski('#skF_2', B_44))), inference(demodulation, [status(thm), theory('equality')], [c_2766, c_136])).
% 5.76/2.20  tff(c_2739, plain, (![A_252]: (~r1_tarski(k1_relat_1('#skF_3'), A_252) | m1_subset_1('#skF_3', k1_zfmisc_1(k1_xboole_0)))), inference(splitRight, [status(thm)], [c_2124])).
% 5.76/2.20  tff(c_2822, plain, (![A_252]: (~r1_tarski(k1_relat_1('#skF_3'), A_252) | m1_subset_1('#skF_3', k1_zfmisc_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_2766, c_2739])).
% 5.76/2.20  tff(c_2851, plain, (![A_299]: (~r1_tarski(k1_relat_1('#skF_3'), A_299))), inference(splitLeft, [status(thm)], [c_2822])).
% 5.76/2.20  tff(c_2856, plain, $false, inference(resolution, [status(thm)], [c_10, c_2851])).
% 5.76/2.20  tff(c_2857, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_2'))), inference(splitRight, [status(thm)], [c_2822])).
% 5.76/2.20  tff(c_2976, plain, (r1_tarski('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_2857, c_26])).
% 5.76/2.20  tff(c_2979, plain, ('#skF_2'='#skF_3' | ~r1_tarski('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_2976, c_6])).
% 5.76/2.20  tff(c_2982, plain, ('#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_2808, c_2979])).
% 5.76/2.20  tff(c_127, plain, (![B_43]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(B_43)))), inference(superposition, [status(thm), theory('equality')], [c_122, c_57])).
% 5.76/2.20  tff(c_1610, plain, (![A_189, B_190]: (k1_relset_1(A_189, B_190, k1_xboole_0)=k1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_127, c_1591])).
% 5.76/2.20  tff(c_20, plain, (![B_8]: (k2_zfmisc_1(k1_xboole_0, B_8)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_50])).
% 5.76/2.20  tff(c_40, plain, (![C_26, B_25]: (v1_funct_2(C_26, k1_xboole_0, B_25) | k1_relset_1(k1_xboole_0, B_25, C_26)!=k1_xboole_0 | ~m1_subset_1(C_26, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_25))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 5.76/2.20  tff(c_2012, plain, (![C_239, B_240]: (v1_funct_2(C_239, k1_xboole_0, B_240) | k1_relset_1(k1_xboole_0, B_240, C_239)!=k1_xboole_0 | ~m1_subset_1(C_239, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_40])).
% 5.76/2.20  tff(c_2015, plain, (![B_240]: (v1_funct_2(k1_xboole_0, k1_xboole_0, B_240) | k1_relset_1(k1_xboole_0, B_240, k1_xboole_0)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_127, c_2012])).
% 5.76/2.20  tff(c_2023, plain, (![B_240]: (v1_funct_2(k1_xboole_0, k1_xboole_0, B_240) | k1_relat_1(k1_xboole_0)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1610, c_2015])).
% 5.76/2.20  tff(c_2027, plain, (k1_relat_1(k1_xboole_0)!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_2023])).
% 5.76/2.20  tff(c_2779, plain, (k1_relat_1('#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_2766, c_2766, c_2027])).
% 5.76/2.20  tff(c_2988, plain, (k1_relat_1('#skF_3')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_2982, c_2982, c_2779])).
% 5.76/2.20  tff(c_36, plain, (![A_24]: (v1_funct_2(k1_xboole_0, A_24, k1_xboole_0) | k1_xboole_0=A_24 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(A_24, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 5.76/2.20  tff(c_60, plain, (![A_24]: (v1_funct_2(k1_xboole_0, A_24, k1_xboole_0) | k1_xboole_0=A_24 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_36])).
% 5.76/2.20  tff(c_1563, plain, (![A_24]: (v1_funct_2(k1_xboole_0, A_24, k1_xboole_0) | k1_xboole_0=A_24)), inference(demodulation, [status(thm), theory('equality')], [c_127, c_60])).
% 5.76/2.20  tff(c_2801, plain, (![A_24]: (v1_funct_2('#skF_2', A_24, '#skF_2') | A_24='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2766, c_2766, c_2766, c_1563])).
% 5.76/2.20  tff(c_3336, plain, (![A_337]: (v1_funct_2('#skF_3', A_337, '#skF_3') | A_337='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2982, c_2982, c_2982, c_2801])).
% 5.76/2.20  tff(c_2994, plain, (~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2982, c_88])).
% 5.76/2.20  tff(c_3339, plain, (k1_relat_1('#skF_3')='#skF_3'), inference(resolution, [status(thm)], [c_3336, c_2994])).
% 5.76/2.20  tff(c_3343, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2988, c_3339])).
% 5.76/2.20  tff(c_3345, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(splitRight, [status(thm)], [c_2023])).
% 5.76/2.20  tff(c_4144, plain, (k1_relat_1('#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_4124, c_4124, c_3345])).
% 5.76/2.20  tff(c_4448, plain, (k1_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_4438, c_4438, c_4144])).
% 5.76/2.20  tff(c_3520, plain, (![C_353, B_354]: (m1_subset_1(C_353, k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski(k2_relat_1(C_353), B_354) | ~r1_tarski(k1_relat_1(C_353), k1_xboole_0) | ~v1_relat_1(C_353))), inference(superposition, [status(thm), theory('equality')], [c_20, c_1735])).
% 5.76/2.20  tff(c_3523, plain, (![B_354]: (m1_subset_1('#skF_3', k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski('#skF_2', B_354) | ~r1_tarski(k1_relat_1('#skF_3'), k1_xboole_0) | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1533, c_3520])).
% 5.76/2.20  tff(c_3532, plain, (![B_354]: (m1_subset_1('#skF_3', k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski('#skF_2', B_354) | ~r1_tarski(k1_relat_1('#skF_3'), k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_3523])).
% 5.76/2.20  tff(c_3545, plain, (~r1_tarski(k1_relat_1('#skF_3'), k1_xboole_0)), inference(splitLeft, [status(thm)], [c_3532])).
% 5.76/2.20  tff(c_4137, plain, (~r1_tarski(k1_relat_1('#skF_3'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4124, c_3545])).
% 5.76/2.20  tff(c_4534, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10, c_4448, c_4438, c_4137])).
% 5.76/2.20  tff(c_4536, plain, (r1_tarski(k1_relat_1('#skF_3'), k1_xboole_0)), inference(splitRight, [status(thm)], [c_3532])).
% 5.76/2.20  tff(c_3534, plain, (![C_353]: (m1_subset_1(C_353, k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski(k1_relat_1(C_353), k1_xboole_0) | ~v1_relat_1(C_353))), inference(resolution, [status(thm)], [c_10, c_3520])).
% 5.76/2.20  tff(c_4539, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_xboole_0)) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_4536, c_3534])).
% 5.76/2.20  tff(c_4560, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_4539])).
% 5.76/2.20  tff(c_30, plain, (![C_17, B_16, A_15]: (~v1_xboole_0(C_17) | ~m1_subset_1(B_16, k1_zfmisc_1(C_17)) | ~r2_hidden(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_65])).
% 5.76/2.20  tff(c_4609, plain, (![A_15]: (~v1_xboole_0(k1_xboole_0) | ~r2_hidden(A_15, '#skF_3'))), inference(resolution, [status(thm)], [c_4560, c_30])).
% 5.76/2.20  tff(c_4622, plain, (![A_424]: (~r2_hidden(A_424, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_4609])).
% 5.76/2.20  tff(c_4627, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_4, c_4622])).
% 5.76/2.20  tff(c_3344, plain, (![B_240]: (v1_funct_2(k1_xboole_0, k1_xboole_0, B_240))), inference(splitRight, [status(thm)], [c_2023])).
% 5.76/2.20  tff(c_4637, plain, (![B_240]: (v1_funct_2('#skF_3', '#skF_3', B_240))), inference(demodulation, [status(thm), theory('equality')], [c_4627, c_4627, c_3344])).
% 5.76/2.20  tff(c_4549, plain, (~v1_xboole_0(k1_xboole_0) | k1_relat_1('#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_4536, c_1590])).
% 5.76/2.20  tff(c_4568, plain, (k1_relat_1('#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_2, c_4549])).
% 5.76/2.20  tff(c_4575, plain, (~v1_funct_2('#skF_3', k1_xboole_0, '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4568, c_88])).
% 5.76/2.20  tff(c_4629, plain, (~v1_funct_2('#skF_3', '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4627, c_4575])).
% 5.76/2.20  tff(c_4821, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4637, c_4629])).
% 5.76/2.20  tff(c_4822, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2')))), inference(splitRight, [status(thm)], [c_56])).
% 5.76/2.20  tff(c_5258, plain, (~r1_tarski(k2_relat_1('#skF_3'), '#skF_2') | ~r1_tarski(k1_relat_1('#skF_3'), k1_relat_1('#skF_3')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_5247, c_4822])).
% 5.76/2.20  tff(c_5271, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54, c_10, c_50, c_5258])).
% 5.76/2.20  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.76/2.20  
% 5.76/2.20  Inference rules
% 5.76/2.20  ----------------------
% 5.76/2.20  #Ref     : 0
% 5.76/2.20  #Sup     : 1055
% 5.76/2.20  #Fact    : 0
% 5.76/2.20  #Define  : 0
% 5.76/2.20  #Split   : 28
% 5.76/2.20  #Chain   : 0
% 5.76/2.20  #Close   : 0
% 5.76/2.20  
% 5.76/2.20  Ordering : KBO
% 5.76/2.20  
% 5.76/2.20  Simplification rules
% 5.76/2.20  ----------------------
% 5.76/2.20  #Subsume      : 157
% 5.76/2.20  #Demod        : 1346
% 5.76/2.20  #Tautology    : 467
% 5.76/2.20  #SimpNegUnit  : 11
% 5.76/2.20  #BackRed      : 386
% 5.76/2.20  
% 5.76/2.20  #Partial instantiations: 0
% 5.76/2.20  #Strategies tried      : 1
% 5.76/2.20  
% 5.76/2.20  Timing (in seconds)
% 5.76/2.20  ----------------------
% 5.76/2.20  Preprocessing        : 0.32
% 5.76/2.20  Parsing              : 0.17
% 5.76/2.20  CNF conversion       : 0.02
% 5.76/2.20  Main loop            : 1.05
% 5.76/2.20  Inferencing          : 0.35
% 5.76/2.20  Reduction            : 0.35
% 5.76/2.20  Demodulation         : 0.24
% 5.76/2.20  BG Simplification    : 0.04
% 5.76/2.20  Subsumption          : 0.20
% 5.76/2.20  Abstraction          : 0.06
% 5.76/2.20  MUC search           : 0.00
% 5.76/2.20  Cooper               : 0.00
% 5.76/2.20  Total                : 1.43
% 5.76/2.20  Index Insertion      : 0.00
% 5.76/2.20  Index Deletion       : 0.00
% 5.76/2.20  Index Matching       : 0.00
% 5.76/2.20  BG Taut test         : 0.00
%------------------------------------------------------------------------------
