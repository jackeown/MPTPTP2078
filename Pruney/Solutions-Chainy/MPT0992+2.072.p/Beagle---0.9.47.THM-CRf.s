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
% DateTime   : Thu Dec  3 10:13:42 EST 2020

% Result     : Theorem 7.66s
% Output     : CNFRefutation 7.93s
% Verified   : 
% Statistics : Number of formulae       :  198 (4431 expanded)
%              Number of leaves         :   37 (1379 expanded)
%              Depth                    :   20
%              Number of atoms          :  347 (13904 expanded)
%              Number of equality atoms :   87 (5577 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_partfun1 > k1_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

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

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

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

tff(k2_partfun1,type,(
    k2_partfun1: ( $i * $i * $i * $i ) > $i )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_138,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( r1_tarski(C,A)
         => ( ( B = k1_xboole_0
              & A != k1_xboole_0 )
            | ( v1_funct_1(k2_partfun1(A,B,D,C))
              & v1_funct_2(k2_partfun1(A,B,D,C),C,B)
              & m1_subset_1(k2_partfun1(A,B,D,C),k1_zfmisc_1(k2_zfmisc_1(C,B))) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_funct_2)).

tff(f_54,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_46,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_74,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

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

tff(f_64,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => k1_relat_1(k7_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).

tff(f_106,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_100,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( v1_funct_1(k2_partfun1(A,B,C,D))
        & m1_subset_1(k2_partfun1(A,B,C,D),k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_partfun1)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_118,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(k2_relat_1(B),A)
       => ( v1_funct_1(B)
          & v1_funct_2(B,k1_relat_1(B),A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B),A))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).

tff(f_39,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_35,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_29,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k7_relat_1(B,A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_relat_1)).

tff(c_60,plain,(
    r1_tarski('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_20,plain,(
    ! [A_11,B_12] : v1_relat_1(k2_zfmisc_1(A_11,B_12)) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_62,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_147,plain,(
    ! [B_50,A_51] :
      ( v1_relat_1(B_50)
      | ~ m1_subset_1(B_50,k1_zfmisc_1(A_51))
      | ~ v1_relat_1(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_153,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_62,c_147])).

tff(c_157,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_153])).

tff(c_58,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_71,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_64,plain,(
    v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_4615,plain,(
    ! [A_568,B_569,C_570] :
      ( k1_relset_1(A_568,B_569,C_570) = k1_relat_1(C_570)
      | ~ m1_subset_1(C_570,k1_zfmisc_1(k2_zfmisc_1(A_568,B_569))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_4634,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_62,c_4615])).

tff(c_5194,plain,(
    ! [B_638,A_639,C_640] :
      ( k1_xboole_0 = B_638
      | k1_relset_1(A_639,B_638,C_640) = A_639
      | ~ v1_funct_2(C_640,A_639,B_638)
      | ~ m1_subset_1(C_640,k1_zfmisc_1(k2_zfmisc_1(A_639,B_638))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_5207,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_62,c_5194])).

tff(c_5221,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_4634,c_5207])).

tff(c_5222,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_71,c_5221])).

tff(c_24,plain,(
    ! [B_16,A_15] :
      ( k1_relat_1(k7_relat_1(B_16,A_15)) = A_15
      | ~ r1_tarski(A_15,k1_relat_1(B_16))
      | ~ v1_relat_1(B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_5234,plain,(
    ! [A_15] :
      ( k1_relat_1(k7_relat_1('#skF_4',A_15)) = A_15
      | ~ r1_tarski(A_15,'#skF_1')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5222,c_24])).

tff(c_5256,plain,(
    ! [A_642] :
      ( k1_relat_1(k7_relat_1('#skF_4',A_642)) = A_642
      | ~ r1_tarski(A_642,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_157,c_5234])).

tff(c_66,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_5056,plain,(
    ! [A_628,B_629,C_630,D_631] :
      ( k2_partfun1(A_628,B_629,C_630,D_631) = k7_relat_1(C_630,D_631)
      | ~ m1_subset_1(C_630,k1_zfmisc_1(k2_zfmisc_1(A_628,B_629)))
      | ~ v1_funct_1(C_630) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_5065,plain,(
    ! [D_631] :
      ( k2_partfun1('#skF_1','#skF_2','#skF_4',D_631) = k7_relat_1('#skF_4',D_631)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_62,c_5056])).

tff(c_5077,plain,(
    ! [D_631] : k2_partfun1('#skF_1','#skF_2','#skF_4',D_631) = k7_relat_1('#skF_4',D_631) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_5065])).

tff(c_1323,plain,(
    ! [A_215,B_216,C_217,D_218] :
      ( k2_partfun1(A_215,B_216,C_217,D_218) = k7_relat_1(C_217,D_218)
      | ~ m1_subset_1(C_217,k1_zfmisc_1(k2_zfmisc_1(A_215,B_216)))
      | ~ v1_funct_1(C_217) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_1330,plain,(
    ! [D_218] :
      ( k2_partfun1('#skF_1','#skF_2','#skF_4',D_218) = k7_relat_1('#skF_4',D_218)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_62,c_1323])).

tff(c_1339,plain,(
    ! [D_218] : k2_partfun1('#skF_1','#skF_2','#skF_4',D_218) = k7_relat_1('#skF_4',D_218) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_1330])).

tff(c_1620,plain,(
    ! [A_255,B_256,C_257,D_258] :
      ( m1_subset_1(k2_partfun1(A_255,B_256,C_257,D_258),k1_zfmisc_1(k2_zfmisc_1(A_255,B_256)))
      | ~ m1_subset_1(C_257,k1_zfmisc_1(k2_zfmisc_1(A_255,B_256)))
      | ~ v1_funct_1(C_257) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_1648,plain,(
    ! [D_218] :
      ( m1_subset_1(k7_relat_1('#skF_4',D_218),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1339,c_1620])).

tff(c_1680,plain,(
    ! [D_259] : m1_subset_1(k7_relat_1('#skF_4',D_259),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_62,c_1648])).

tff(c_26,plain,(
    ! [C_19,B_18,A_17] :
      ( v5_relat_1(C_19,B_18)
      | ~ m1_subset_1(C_19,k1_zfmisc_1(k2_zfmisc_1(A_17,B_18))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_1720,plain,(
    ! [D_259] : v5_relat_1(k7_relat_1('#skF_4',D_259),'#skF_2') ),
    inference(resolution,[status(thm)],[c_1680,c_26])).

tff(c_14,plain,(
    ! [B_8,A_6] :
      ( v1_relat_1(B_8)
      | ~ m1_subset_1(B_8,k1_zfmisc_1(A_6))
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_1702,plain,(
    ! [D_259] :
      ( v1_relat_1(k7_relat_1('#skF_4',D_259))
      | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_1680,c_14])).

tff(c_1723,plain,(
    ! [D_259] : v1_relat_1(k7_relat_1('#skF_4',D_259)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_1702])).

tff(c_18,plain,(
    ! [B_10,A_9] :
      ( r1_tarski(k2_relat_1(B_10),A_9)
      | ~ v5_relat_1(B_10,A_9)
      | ~ v1_relat_1(B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_1076,plain,(
    ! [A_183,B_184,C_185,D_186] :
      ( v1_funct_1(k2_partfun1(A_183,B_184,C_185,D_186))
      | ~ m1_subset_1(C_185,k1_zfmisc_1(k2_zfmisc_1(A_183,B_184)))
      | ~ v1_funct_1(C_185) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_1081,plain,(
    ! [D_186] :
      ( v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4',D_186))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_62,c_1076])).

tff(c_1089,plain,(
    ! [D_186] : v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4',D_186)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_1081])).

tff(c_1340,plain,(
    ! [D_186] : v1_funct_1(k7_relat_1('#skF_4',D_186)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1339,c_1089])).

tff(c_934,plain,(
    ! [A_165,B_166,C_167] :
      ( k1_relset_1(A_165,B_166,C_167) = k1_relat_1(C_167)
      | ~ m1_subset_1(C_167,k1_zfmisc_1(k2_zfmisc_1(A_165,B_166))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_949,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_62,c_934])).

tff(c_1466,plain,(
    ! [B_247,A_248,C_249] :
      ( k1_xboole_0 = B_247
      | k1_relset_1(A_248,B_247,C_249) = A_248
      | ~ v1_funct_2(C_249,A_248,B_247)
      | ~ m1_subset_1(C_249,k1_zfmisc_1(k2_zfmisc_1(A_248,B_247))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_1476,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_62,c_1466])).

tff(c_1487,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_949,c_1476])).

tff(c_1488,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_71,c_1487])).

tff(c_1500,plain,(
    ! [A_15] :
      ( k1_relat_1(k7_relat_1('#skF_4',A_15)) = A_15
      | ~ r1_tarski(A_15,'#skF_1')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1488,c_24])).

tff(c_1508,plain,(
    ! [A_15] :
      ( k1_relat_1(k7_relat_1('#skF_4',A_15)) = A_15
      | ~ r1_tarski(A_15,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_157,c_1500])).

tff(c_1166,plain,(
    ! [B_196,A_197] :
      ( m1_subset_1(B_196,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_196),A_197)))
      | ~ r1_tarski(k2_relat_1(B_196),A_197)
      | ~ v1_funct_1(B_196)
      | ~ v1_relat_1(B_196) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_10,plain,(
    ! [A_4,B_5] :
      ( r1_tarski(A_4,B_5)
      | ~ m1_subset_1(A_4,k1_zfmisc_1(B_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_2756,plain,(
    ! [B_407,A_408] :
      ( r1_tarski(B_407,k2_zfmisc_1(k1_relat_1(B_407),A_408))
      | ~ r1_tarski(k2_relat_1(B_407),A_408)
      | ~ v1_funct_1(B_407)
      | ~ v1_relat_1(B_407) ) ),
    inference(resolution,[status(thm)],[c_1166,c_10])).

tff(c_2813,plain,(
    ! [A_15,A_408] :
      ( r1_tarski(k7_relat_1('#skF_4',A_15),k2_zfmisc_1(A_15,A_408))
      | ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_4',A_15)),A_408)
      | ~ v1_funct_1(k7_relat_1('#skF_4',A_15))
      | ~ v1_relat_1(k7_relat_1('#skF_4',A_15))
      | ~ r1_tarski(A_15,'#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1508,c_2756])).

tff(c_3081,plain,(
    ! [A_433,A_434] :
      ( r1_tarski(k7_relat_1('#skF_4',A_433),k2_zfmisc_1(A_433,A_434))
      | ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_4',A_433)),A_434)
      | ~ r1_tarski(A_433,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1723,c_1340,c_2813])).

tff(c_3087,plain,(
    ! [A_433,A_9] :
      ( r1_tarski(k7_relat_1('#skF_4',A_433),k2_zfmisc_1(A_433,A_9))
      | ~ r1_tarski(A_433,'#skF_1')
      | ~ v5_relat_1(k7_relat_1('#skF_4',A_433),A_9)
      | ~ v1_relat_1(k7_relat_1('#skF_4',A_433)) ) ),
    inference(resolution,[status(thm)],[c_18,c_3081])).

tff(c_4274,plain,(
    ! [A_529,A_530] :
      ( r1_tarski(k7_relat_1('#skF_4',A_529),k2_zfmisc_1(A_529,A_530))
      | ~ r1_tarski(A_529,'#skF_1')
      | ~ v5_relat_1(k7_relat_1('#skF_4',A_529),A_530) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1723,c_3087])).

tff(c_12,plain,(
    ! [A_4,B_5] :
      ( m1_subset_1(A_4,k1_zfmisc_1(B_5))
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_571,plain,(
    ! [A_114,B_115,C_116,D_117] :
      ( v1_funct_1(k2_partfun1(A_114,B_115,C_116,D_117))
      | ~ m1_subset_1(C_116,k1_zfmisc_1(k2_zfmisc_1(A_114,B_115)))
      | ~ v1_funct_1(C_116) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_576,plain,(
    ! [D_117] :
      ( v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4',D_117))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_62,c_571])).

tff(c_584,plain,(
    ! [D_117] : v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4',D_117)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_576])).

tff(c_56,plain,
    ( ~ m1_subset_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_2(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_3','#skF_2')
    | ~ v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_158,plain,(
    ~ v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_612,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_584,c_158])).

tff(c_613,plain,
    ( ~ v1_funct_2(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_3','#skF_2')
    | ~ m1_subset_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_638,plain,(
    ~ m1_subset_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_613])).

tff(c_692,plain,(
    ~ r1_tarski(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),k2_zfmisc_1('#skF_3','#skF_2')) ),
    inference(resolution,[status(thm)],[c_12,c_638])).

tff(c_1341,plain,(
    ~ r1_tarski(k7_relat_1('#skF_4','#skF_3'),k2_zfmisc_1('#skF_3','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1339,c_692])).

tff(c_4286,plain,
    ( ~ r1_tarski('#skF_3','#skF_1')
    | ~ v5_relat_1(k7_relat_1('#skF_4','#skF_3'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_4274,c_1341])).

tff(c_4318,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1720,c_60,c_4286])).

tff(c_4320,plain,(
    m1_subset_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_613])).

tff(c_4632,plain,(
    k1_relset_1('#skF_3','#skF_2',k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')) = k1_relat_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')) ),
    inference(resolution,[status(thm)],[c_4320,c_4615])).

tff(c_5080,plain,(
    k1_relset_1('#skF_3','#skF_2',k7_relat_1('#skF_4','#skF_3')) = k1_relat_1(k7_relat_1('#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5077,c_5077,c_4632])).

tff(c_4319,plain,(
    ~ v1_funct_2(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_613])).

tff(c_5086,plain,(
    ~ v1_funct_2(k7_relat_1('#skF_4','#skF_3'),'#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5077,c_4319])).

tff(c_5085,plain,(
    m1_subset_1(k7_relat_1('#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5077,c_4320])).

tff(c_38,plain,(
    ! [B_24,C_25,A_23] :
      ( k1_xboole_0 = B_24
      | v1_funct_2(C_25,A_23,B_24)
      | k1_relset_1(A_23,B_24,C_25) != A_23
      | ~ m1_subset_1(C_25,k1_zfmisc_1(k2_zfmisc_1(A_23,B_24))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_5147,plain,
    ( k1_xboole_0 = '#skF_2'
    | v1_funct_2(k7_relat_1('#skF_4','#skF_3'),'#skF_3','#skF_2')
    | k1_relset_1('#skF_3','#skF_2',k7_relat_1('#skF_4','#skF_3')) != '#skF_3' ),
    inference(resolution,[status(thm)],[c_5085,c_38])).

tff(c_5169,plain,(
    k1_relset_1('#skF_3','#skF_2',k7_relat_1('#skF_4','#skF_3')) != '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_5086,c_71,c_5147])).

tff(c_5188,plain,(
    k1_relat_1(k7_relat_1('#skF_4','#skF_3')) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5080,c_5169])).

tff(c_5262,plain,(
    ~ r1_tarski('#skF_3','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_5256,c_5188])).

tff(c_5287,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_5262])).

tff(c_5288,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_6,plain,(
    ! [A_2] : k2_zfmisc_1(A_2,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_5301,plain,(
    ! [A_2] : k2_zfmisc_1(A_2,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5288,c_5288,c_6])).

tff(c_5289,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_5294,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5288,c_5289])).

tff(c_5341,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5301,c_5294,c_62])).

tff(c_5368,plain,(
    ! [A_653,B_654] :
      ( r1_tarski(A_653,B_654)
      | ~ m1_subset_1(A_653,k1_zfmisc_1(B_654)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_5376,plain,(
    r1_tarski('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_5341,c_5368])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ r1_tarski(A_1,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_5330,plain,(
    ! [A_1] :
      ( A_1 = '#skF_1'
      | ~ r1_tarski(A_1,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5288,c_5288,c_2])).

tff(c_5391,plain,(
    '#skF_1' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_5376,c_5330])).

tff(c_5295,plain,(
    v1_funct_2('#skF_4','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5294,c_64])).

tff(c_5398,plain,(
    v1_funct_2('#skF_4','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5391,c_5391,c_5295])).

tff(c_5395,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5391,c_5341])).

tff(c_8,plain,(
    ! [B_3] : k2_zfmisc_1(k1_xboole_0,B_3) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_5311,plain,(
    ! [B_3] : k2_zfmisc_1('#skF_1',B_3) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5288,c_5288,c_8])).

tff(c_5399,plain,(
    ! [B_3] : k2_zfmisc_1('#skF_4',B_3) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5391,c_5391,c_5311])).

tff(c_6304,plain,(
    ! [C_791,B_792,A_793] :
      ( v5_relat_1(C_791,B_792)
      | ~ m1_subset_1(C_791,k1_zfmisc_1(k2_zfmisc_1(A_793,B_792))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_6379,plain,(
    ! [C_799,B_800] :
      ( v5_relat_1(C_799,B_800)
      | ~ m1_subset_1(C_799,k1_zfmisc_1('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5399,c_6304])).

tff(c_6385,plain,(
    ! [B_800] : v5_relat_1('#skF_4',B_800) ),
    inference(resolution,[status(thm)],[c_5395,c_6379])).

tff(c_5302,plain,(
    ! [A_645] : k2_zfmisc_1(A_645,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5288,c_5288,c_6])).

tff(c_5306,plain,(
    v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_5302,c_20])).

tff(c_5347,plain,(
    ! [B_648,A_649] :
      ( r1_tarski(k7_relat_1(B_648,A_649),B_648)
      | ~ v1_relat_1(B_648) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_5351,plain,(
    ! [A_649] :
      ( k7_relat_1('#skF_1',A_649) = '#skF_1'
      | ~ v1_relat_1('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_5347,c_5330])).

tff(c_5354,plain,(
    ! [A_649] : k7_relat_1('#skF_1',A_649) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5306,c_5351])).

tff(c_5393,plain,(
    ! [A_649] : k7_relat_1('#skF_4',A_649) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5391,c_5391,c_5354])).

tff(c_5401,plain,(
    ! [A_2] : k2_zfmisc_1(A_2,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5391,c_5391,c_5301])).

tff(c_7805,plain,(
    ! [A_949,B_950,C_951,D_952] :
      ( k2_partfun1(A_949,B_950,C_951,D_952) = k7_relat_1(C_951,D_952)
      | ~ m1_subset_1(C_951,k1_zfmisc_1(k2_zfmisc_1(A_949,B_950)))
      | ~ v1_funct_1(C_951) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_8583,plain,(
    ! [A_1014,C_1015,D_1016] :
      ( k2_partfun1(A_1014,'#skF_4',C_1015,D_1016) = k7_relat_1(C_1015,D_1016)
      | ~ m1_subset_1(C_1015,k1_zfmisc_1('#skF_4'))
      | ~ v1_funct_1(C_1015) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5401,c_7805])).

tff(c_8587,plain,(
    ! [A_1014,D_1016] :
      ( k2_partfun1(A_1014,'#skF_4','#skF_4',D_1016) = k7_relat_1('#skF_4',D_1016)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_5395,c_8583])).

tff(c_8594,plain,(
    ! [A_1014,D_1016] : k2_partfun1(A_1014,'#skF_4','#skF_4',D_1016) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_5393,c_8587])).

tff(c_5377,plain,(
    ! [B_655,A_656] :
      ( v1_relat_1(B_655)
      | ~ m1_subset_1(B_655,k1_zfmisc_1(A_656))
      | ~ v1_relat_1(A_656) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_5383,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_5341,c_5377])).

tff(c_5387,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5306,c_5383])).

tff(c_8208,plain,(
    ! [B_984,C_985,D_986] :
      ( k2_partfun1('#skF_4',B_984,C_985,D_986) = k7_relat_1(C_985,D_986)
      | ~ m1_subset_1(C_985,k1_zfmisc_1('#skF_4'))
      | ~ v1_funct_1(C_985) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5399,c_7805])).

tff(c_8212,plain,(
    ! [B_984,D_986] :
      ( k2_partfun1('#skF_4',B_984,'#skF_4',D_986) = k7_relat_1('#skF_4',D_986)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_5395,c_8208])).

tff(c_8219,plain,(
    ! [B_984,D_986] : k2_partfun1('#skF_4',B_984,'#skF_4',D_986) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_5393,c_8212])).

tff(c_6316,plain,(
    ! [C_794] :
      ( v5_relat_1(C_794,'#skF_4')
      | ~ m1_subset_1(C_794,k1_zfmisc_1('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5401,c_6304])).

tff(c_6324,plain,(
    v5_relat_1('#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_5395,c_6316])).

tff(c_6279,plain,(
    ! [B_786,A_787] :
      ( r1_tarski(k2_relat_1(B_786),A_787)
      | ~ v5_relat_1(B_786,A_787)
      | ~ v1_relat_1(B_786) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_5397,plain,(
    ! [A_1] :
      ( A_1 = '#skF_4'
      | ~ r1_tarski(A_1,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5391,c_5391,c_5330])).

tff(c_6293,plain,(
    ! [B_786] :
      ( k2_relat_1(B_786) = '#skF_4'
      | ~ v5_relat_1(B_786,'#skF_4')
      | ~ v1_relat_1(B_786) ) ),
    inference(resolution,[status(thm)],[c_6279,c_5397])).

tff(c_6328,plain,
    ( k2_relat_1('#skF_4') = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_6324,c_6293])).

tff(c_6331,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5387,c_6328])).

tff(c_6338,plain,(
    ! [A_9] :
      ( r1_tarski('#skF_4',A_9)
      | ~ v5_relat_1('#skF_4',A_9)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6331,c_18])).

tff(c_6344,plain,(
    ! [A_9] :
      ( r1_tarski('#skF_4',A_9)
      | ~ v5_relat_1('#skF_4',A_9) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5387,c_6338])).

tff(c_6388,plain,(
    ! [A_9] : r1_tarski('#skF_4',A_9) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6385,c_6344])).

tff(c_7468,plain,(
    ! [A_903,B_904,C_905,D_906] :
      ( v1_funct_1(k2_partfun1(A_903,B_904,C_905,D_906))
      | ~ m1_subset_1(C_905,k1_zfmisc_1(k2_zfmisc_1(A_903,B_904)))
      | ~ v1_funct_1(C_905) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_7514,plain,(
    ! [A_925,B_926,A_927,D_928] :
      ( v1_funct_1(k2_partfun1(A_925,B_926,A_927,D_928))
      | ~ v1_funct_1(A_927)
      | ~ r1_tarski(A_927,k2_zfmisc_1(A_925,B_926)) ) ),
    inference(resolution,[status(thm)],[c_12,c_7468])).

tff(c_7517,plain,(
    ! [A_925,B_926,D_928] :
      ( v1_funct_1(k2_partfun1(A_925,B_926,'#skF_4',D_928))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_6388,c_7514])).

tff(c_7530,plain,(
    ! [A_925,B_926,D_928] : v1_funct_1(k2_partfun1(A_925,B_926,'#skF_4',D_928)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_7517])).

tff(c_7538,plain,(
    ! [B_932,A_933] :
      ( m1_subset_1(B_932,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_932),A_933)))
      | ~ r1_tarski(k2_relat_1(B_932),A_933)
      | ~ v1_funct_1(B_932)
      | ~ v1_relat_1(B_932) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_7625,plain,(
    ! [B_938] :
      ( m1_subset_1(B_938,k1_zfmisc_1('#skF_4'))
      | ~ r1_tarski(k2_relat_1(B_938),'#skF_4')
      | ~ v1_funct_1(B_938)
      | ~ v1_relat_1(B_938) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5401,c_7538])).

tff(c_7656,plain,(
    ! [B_941] :
      ( m1_subset_1(B_941,k1_zfmisc_1('#skF_4'))
      | ~ v1_funct_1(B_941)
      | ~ v5_relat_1(B_941,'#skF_4')
      | ~ v1_relat_1(B_941) ) ),
    inference(resolution,[status(thm)],[c_18,c_7625])).

tff(c_5402,plain,(
    '#skF_2' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5391,c_5294])).

tff(c_5331,plain,(
    ! [A_647] :
      ( A_647 = '#skF_1'
      | ~ r1_tarski(A_647,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5288,c_5288,c_2])).

tff(c_5335,plain,(
    '#skF_3' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_60,c_5331])).

tff(c_5396,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5391,c_5335])).

tff(c_6101,plain,(
    ! [A_755,B_756,C_757,D_758] :
      ( v1_funct_1(k2_partfun1(A_755,B_756,C_757,D_758))
      | ~ m1_subset_1(C_757,k1_zfmisc_1(k2_zfmisc_1(A_755,B_756)))
      | ~ v1_funct_1(C_757) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_6110,plain,(
    ! [A_759,C_760,D_761] :
      ( v1_funct_1(k2_partfun1(A_759,'#skF_4',C_760,D_761))
      | ~ m1_subset_1(C_760,k1_zfmisc_1('#skF_4'))
      | ~ v1_funct_1(C_760) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5401,c_6101])).

tff(c_6112,plain,(
    ! [A_759,D_761] :
      ( v1_funct_1(k2_partfun1(A_759,'#skF_4','#skF_4',D_761))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_5395,c_6110])).

tff(c_6118,plain,(
    ! [A_759,D_761] : v1_funct_1(k2_partfun1(A_759,'#skF_4','#skF_4',D_761)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_6112])).

tff(c_5409,plain,
    ( ~ m1_subset_1(k2_partfun1('#skF_4','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_2(k2_partfun1('#skF_4','#skF_2','#skF_4','#skF_3'),'#skF_3','#skF_2')
    | ~ v1_funct_1(k2_partfun1('#skF_4','#skF_2','#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5391,c_5391,c_5391,c_56])).

tff(c_5410,plain,(
    ~ v1_funct_1(k2_partfun1('#skF_4','#skF_2','#skF_4','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_5409])).

tff(c_5500,plain,(
    ~ v1_funct_1(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5402,c_5396,c_5410])).

tff(c_6122,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6118,c_5500])).

tff(c_6123,plain,
    ( ~ v1_funct_2(k2_partfun1('#skF_4','#skF_2','#skF_4','#skF_3'),'#skF_3','#skF_2')
    | ~ m1_subset_1(k2_partfun1('#skF_4','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_5409])).

tff(c_6252,plain,
    ( ~ v1_funct_2(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4'),'#skF_4','#skF_4')
    | ~ m1_subset_1(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4'),k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5399,c_5402,c_5402,c_5396,c_5396,c_5402,c_5402,c_5396,c_5396,c_6123])).

tff(c_6253,plain,(
    ~ m1_subset_1(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4'),k1_zfmisc_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_6252])).

tff(c_7671,plain,
    ( ~ v1_funct_1(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4'))
    | ~ v5_relat_1(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4'),'#skF_4')
    | ~ v1_relat_1(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4')) ),
    inference(resolution,[status(thm)],[c_7656,c_6253])).

tff(c_7688,plain,
    ( ~ v5_relat_1(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4'),'#skF_4')
    | ~ v1_relat_1(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7530,c_7671])).

tff(c_7875,plain,(
    ~ v1_relat_1(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_7688])).

tff(c_8221,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8219,c_7875])).

tff(c_8226,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5387,c_8221])).

tff(c_8227,plain,(
    ~ v5_relat_1(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_7688])).

tff(c_8596,plain,(
    ~ v5_relat_1('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8594,c_8227])).

tff(c_8602,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6385,c_8596])).

tff(c_8604,plain,(
    m1_subset_1(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4'),k1_zfmisc_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_6252])).

tff(c_8722,plain,(
    r1_tarski(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_8604,c_10])).

tff(c_8732,plain,(
    k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_8722,c_5397])).

tff(c_8603,plain,(
    ~ v1_funct_2(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4'),'#skF_4','#skF_4') ),
    inference(splitRight,[status(thm)],[c_6252])).

tff(c_8738,plain,(
    ~ v1_funct_2('#skF_4','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8732,c_8603])).

tff(c_8746,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5398,c_8738])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 20:28:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.66/2.64  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.66/2.66  
% 7.66/2.66  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.66/2.67  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_partfun1 > k1_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 7.66/2.67  
% 7.66/2.67  %Foreground sorts:
% 7.66/2.67  
% 7.66/2.67  
% 7.66/2.67  %Background operators:
% 7.66/2.67  
% 7.66/2.67  
% 7.66/2.67  %Foreground operators:
% 7.66/2.67  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 7.66/2.67  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.66/2.67  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 7.66/2.67  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.66/2.67  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.66/2.67  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 7.66/2.67  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 7.66/2.67  tff('#skF_2', type, '#skF_2': $i).
% 7.66/2.67  tff('#skF_3', type, '#skF_3': $i).
% 7.66/2.67  tff('#skF_1', type, '#skF_1': $i).
% 7.66/2.67  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 7.66/2.67  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 7.66/2.67  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.66/2.67  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.66/2.67  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.66/2.67  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.66/2.67  tff('#skF_4', type, '#skF_4': $i).
% 7.66/2.67  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.66/2.67  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 7.66/2.67  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 7.66/2.67  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 7.66/2.67  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.66/2.67  
% 7.93/2.69  tff(f_138, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_tarski(C, A) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | ((v1_funct_1(k2_partfun1(A, B, D, C)) & v1_funct_2(k2_partfun1(A, B, D, C), C, B)) & m1_subset_1(k2_partfun1(A, B, D, C), k1_zfmisc_1(k2_zfmisc_1(C, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_funct_2)).
% 7.93/2.69  tff(f_54, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 7.93/2.69  tff(f_46, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 7.93/2.69  tff(f_74, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 7.93/2.69  tff(f_92, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 7.93/2.69  tff(f_64, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => (k1_relat_1(k7_relat_1(B, A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_relat_1)).
% 7.93/2.69  tff(f_106, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 7.93/2.69  tff(f_100, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (v1_funct_1(k2_partfun1(A, B, C, D)) & m1_subset_1(k2_partfun1(A, B, C, D), k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_partfun1)).
% 7.93/2.69  tff(f_70, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 7.93/2.69  tff(f_52, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 7.93/2.69  tff(f_118, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(k2_relat_1(B), A) => ((v1_funct_1(B) & v1_funct_2(B, k1_relat_1(B), A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B), A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_funct_2)).
% 7.93/2.69  tff(f_39, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 7.93/2.69  tff(f_35, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 7.93/2.69  tff(f_29, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_1)).
% 7.93/2.69  tff(f_58, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k7_relat_1(B, A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_relat_1)).
% 7.93/2.69  tff(c_60, plain, (r1_tarski('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_138])).
% 7.93/2.69  tff(c_20, plain, (![A_11, B_12]: (v1_relat_1(k2_zfmisc_1(A_11, B_12)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 7.93/2.69  tff(c_62, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_138])).
% 7.93/2.69  tff(c_147, plain, (![B_50, A_51]: (v1_relat_1(B_50) | ~m1_subset_1(B_50, k1_zfmisc_1(A_51)) | ~v1_relat_1(A_51))), inference(cnfTransformation, [status(thm)], [f_46])).
% 7.93/2.69  tff(c_153, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_62, c_147])).
% 7.93/2.69  tff(c_157, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_153])).
% 7.93/2.69  tff(c_58, plain, (k1_xboole_0='#skF_1' | k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_138])).
% 7.93/2.69  tff(c_71, plain, (k1_xboole_0!='#skF_2'), inference(splitLeft, [status(thm)], [c_58])).
% 7.93/2.69  tff(c_64, plain, (v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_138])).
% 7.93/2.69  tff(c_4615, plain, (![A_568, B_569, C_570]: (k1_relset_1(A_568, B_569, C_570)=k1_relat_1(C_570) | ~m1_subset_1(C_570, k1_zfmisc_1(k2_zfmisc_1(A_568, B_569))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 7.93/2.69  tff(c_4634, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_62, c_4615])).
% 7.93/2.69  tff(c_5194, plain, (![B_638, A_639, C_640]: (k1_xboole_0=B_638 | k1_relset_1(A_639, B_638, C_640)=A_639 | ~v1_funct_2(C_640, A_639, B_638) | ~m1_subset_1(C_640, k1_zfmisc_1(k2_zfmisc_1(A_639, B_638))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 7.93/2.69  tff(c_5207, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_1' | ~v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_62, c_5194])).
% 7.93/2.69  tff(c_5221, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_64, c_4634, c_5207])).
% 7.93/2.69  tff(c_5222, plain, (k1_relat_1('#skF_4')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_71, c_5221])).
% 7.93/2.69  tff(c_24, plain, (![B_16, A_15]: (k1_relat_1(k7_relat_1(B_16, A_15))=A_15 | ~r1_tarski(A_15, k1_relat_1(B_16)) | ~v1_relat_1(B_16))), inference(cnfTransformation, [status(thm)], [f_64])).
% 7.93/2.69  tff(c_5234, plain, (![A_15]: (k1_relat_1(k7_relat_1('#skF_4', A_15))=A_15 | ~r1_tarski(A_15, '#skF_1') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_5222, c_24])).
% 7.93/2.69  tff(c_5256, plain, (![A_642]: (k1_relat_1(k7_relat_1('#skF_4', A_642))=A_642 | ~r1_tarski(A_642, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_157, c_5234])).
% 7.93/2.69  tff(c_66, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_138])).
% 7.93/2.69  tff(c_5056, plain, (![A_628, B_629, C_630, D_631]: (k2_partfun1(A_628, B_629, C_630, D_631)=k7_relat_1(C_630, D_631) | ~m1_subset_1(C_630, k1_zfmisc_1(k2_zfmisc_1(A_628, B_629))) | ~v1_funct_1(C_630))), inference(cnfTransformation, [status(thm)], [f_106])).
% 7.93/2.69  tff(c_5065, plain, (![D_631]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_631)=k7_relat_1('#skF_4', D_631) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_62, c_5056])).
% 7.93/2.69  tff(c_5077, plain, (![D_631]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_631)=k7_relat_1('#skF_4', D_631))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_5065])).
% 7.93/2.69  tff(c_1323, plain, (![A_215, B_216, C_217, D_218]: (k2_partfun1(A_215, B_216, C_217, D_218)=k7_relat_1(C_217, D_218) | ~m1_subset_1(C_217, k1_zfmisc_1(k2_zfmisc_1(A_215, B_216))) | ~v1_funct_1(C_217))), inference(cnfTransformation, [status(thm)], [f_106])).
% 7.93/2.69  tff(c_1330, plain, (![D_218]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_218)=k7_relat_1('#skF_4', D_218) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_62, c_1323])).
% 7.93/2.69  tff(c_1339, plain, (![D_218]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_218)=k7_relat_1('#skF_4', D_218))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_1330])).
% 7.93/2.69  tff(c_1620, plain, (![A_255, B_256, C_257, D_258]: (m1_subset_1(k2_partfun1(A_255, B_256, C_257, D_258), k1_zfmisc_1(k2_zfmisc_1(A_255, B_256))) | ~m1_subset_1(C_257, k1_zfmisc_1(k2_zfmisc_1(A_255, B_256))) | ~v1_funct_1(C_257))), inference(cnfTransformation, [status(thm)], [f_100])).
% 7.93/2.69  tff(c_1648, plain, (![D_218]: (m1_subset_1(k7_relat_1('#skF_4', D_218), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1339, c_1620])).
% 7.93/2.69  tff(c_1680, plain, (![D_259]: (m1_subset_1(k7_relat_1('#skF_4', D_259), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_62, c_1648])).
% 7.93/2.69  tff(c_26, plain, (![C_19, B_18, A_17]: (v5_relat_1(C_19, B_18) | ~m1_subset_1(C_19, k1_zfmisc_1(k2_zfmisc_1(A_17, B_18))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 7.93/2.69  tff(c_1720, plain, (![D_259]: (v5_relat_1(k7_relat_1('#skF_4', D_259), '#skF_2'))), inference(resolution, [status(thm)], [c_1680, c_26])).
% 7.93/2.69  tff(c_14, plain, (![B_8, A_6]: (v1_relat_1(B_8) | ~m1_subset_1(B_8, k1_zfmisc_1(A_6)) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_46])).
% 7.93/2.69  tff(c_1702, plain, (![D_259]: (v1_relat_1(k7_relat_1('#skF_4', D_259)) | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(resolution, [status(thm)], [c_1680, c_14])).
% 7.93/2.69  tff(c_1723, plain, (![D_259]: (v1_relat_1(k7_relat_1('#skF_4', D_259)))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_1702])).
% 7.93/2.69  tff(c_18, plain, (![B_10, A_9]: (r1_tarski(k2_relat_1(B_10), A_9) | ~v5_relat_1(B_10, A_9) | ~v1_relat_1(B_10))), inference(cnfTransformation, [status(thm)], [f_52])).
% 7.93/2.69  tff(c_1076, plain, (![A_183, B_184, C_185, D_186]: (v1_funct_1(k2_partfun1(A_183, B_184, C_185, D_186)) | ~m1_subset_1(C_185, k1_zfmisc_1(k2_zfmisc_1(A_183, B_184))) | ~v1_funct_1(C_185))), inference(cnfTransformation, [status(thm)], [f_100])).
% 7.93/2.69  tff(c_1081, plain, (![D_186]: (v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_186)) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_62, c_1076])).
% 7.93/2.69  tff(c_1089, plain, (![D_186]: (v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_186)))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_1081])).
% 7.93/2.69  tff(c_1340, plain, (![D_186]: (v1_funct_1(k7_relat_1('#skF_4', D_186)))), inference(demodulation, [status(thm), theory('equality')], [c_1339, c_1089])).
% 7.93/2.69  tff(c_934, plain, (![A_165, B_166, C_167]: (k1_relset_1(A_165, B_166, C_167)=k1_relat_1(C_167) | ~m1_subset_1(C_167, k1_zfmisc_1(k2_zfmisc_1(A_165, B_166))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 7.93/2.69  tff(c_949, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_62, c_934])).
% 7.93/2.69  tff(c_1466, plain, (![B_247, A_248, C_249]: (k1_xboole_0=B_247 | k1_relset_1(A_248, B_247, C_249)=A_248 | ~v1_funct_2(C_249, A_248, B_247) | ~m1_subset_1(C_249, k1_zfmisc_1(k2_zfmisc_1(A_248, B_247))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 7.93/2.69  tff(c_1476, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_1' | ~v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_62, c_1466])).
% 7.93/2.69  tff(c_1487, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_64, c_949, c_1476])).
% 7.93/2.69  tff(c_1488, plain, (k1_relat_1('#skF_4')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_71, c_1487])).
% 7.93/2.69  tff(c_1500, plain, (![A_15]: (k1_relat_1(k7_relat_1('#skF_4', A_15))=A_15 | ~r1_tarski(A_15, '#skF_1') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1488, c_24])).
% 7.93/2.69  tff(c_1508, plain, (![A_15]: (k1_relat_1(k7_relat_1('#skF_4', A_15))=A_15 | ~r1_tarski(A_15, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_157, c_1500])).
% 7.93/2.69  tff(c_1166, plain, (![B_196, A_197]: (m1_subset_1(B_196, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_196), A_197))) | ~r1_tarski(k2_relat_1(B_196), A_197) | ~v1_funct_1(B_196) | ~v1_relat_1(B_196))), inference(cnfTransformation, [status(thm)], [f_118])).
% 7.93/2.69  tff(c_10, plain, (![A_4, B_5]: (r1_tarski(A_4, B_5) | ~m1_subset_1(A_4, k1_zfmisc_1(B_5)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 7.93/2.69  tff(c_2756, plain, (![B_407, A_408]: (r1_tarski(B_407, k2_zfmisc_1(k1_relat_1(B_407), A_408)) | ~r1_tarski(k2_relat_1(B_407), A_408) | ~v1_funct_1(B_407) | ~v1_relat_1(B_407))), inference(resolution, [status(thm)], [c_1166, c_10])).
% 7.93/2.69  tff(c_2813, plain, (![A_15, A_408]: (r1_tarski(k7_relat_1('#skF_4', A_15), k2_zfmisc_1(A_15, A_408)) | ~r1_tarski(k2_relat_1(k7_relat_1('#skF_4', A_15)), A_408) | ~v1_funct_1(k7_relat_1('#skF_4', A_15)) | ~v1_relat_1(k7_relat_1('#skF_4', A_15)) | ~r1_tarski(A_15, '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_1508, c_2756])).
% 7.93/2.69  tff(c_3081, plain, (![A_433, A_434]: (r1_tarski(k7_relat_1('#skF_4', A_433), k2_zfmisc_1(A_433, A_434)) | ~r1_tarski(k2_relat_1(k7_relat_1('#skF_4', A_433)), A_434) | ~r1_tarski(A_433, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_1723, c_1340, c_2813])).
% 7.93/2.69  tff(c_3087, plain, (![A_433, A_9]: (r1_tarski(k7_relat_1('#skF_4', A_433), k2_zfmisc_1(A_433, A_9)) | ~r1_tarski(A_433, '#skF_1') | ~v5_relat_1(k7_relat_1('#skF_4', A_433), A_9) | ~v1_relat_1(k7_relat_1('#skF_4', A_433)))), inference(resolution, [status(thm)], [c_18, c_3081])).
% 7.93/2.69  tff(c_4274, plain, (![A_529, A_530]: (r1_tarski(k7_relat_1('#skF_4', A_529), k2_zfmisc_1(A_529, A_530)) | ~r1_tarski(A_529, '#skF_1') | ~v5_relat_1(k7_relat_1('#skF_4', A_529), A_530))), inference(demodulation, [status(thm), theory('equality')], [c_1723, c_3087])).
% 7.93/2.69  tff(c_12, plain, (![A_4, B_5]: (m1_subset_1(A_4, k1_zfmisc_1(B_5)) | ~r1_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_39])).
% 7.93/2.69  tff(c_571, plain, (![A_114, B_115, C_116, D_117]: (v1_funct_1(k2_partfun1(A_114, B_115, C_116, D_117)) | ~m1_subset_1(C_116, k1_zfmisc_1(k2_zfmisc_1(A_114, B_115))) | ~v1_funct_1(C_116))), inference(cnfTransformation, [status(thm)], [f_100])).
% 7.93/2.69  tff(c_576, plain, (![D_117]: (v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_117)) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_62, c_571])).
% 7.93/2.69  tff(c_584, plain, (![D_117]: (v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_117)))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_576])).
% 7.93/2.69  tff(c_56, plain, (~m1_subset_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_2(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_3', '#skF_2') | ~v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_138])).
% 7.93/2.69  tff(c_158, plain, (~v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))), inference(splitLeft, [status(thm)], [c_56])).
% 7.93/2.69  tff(c_612, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_584, c_158])).
% 7.93/2.69  tff(c_613, plain, (~v1_funct_2(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_3', '#skF_2') | ~m1_subset_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitRight, [status(thm)], [c_56])).
% 7.93/2.69  tff(c_638, plain, (~m1_subset_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitLeft, [status(thm)], [c_613])).
% 7.93/2.69  tff(c_692, plain, (~r1_tarski(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k2_zfmisc_1('#skF_3', '#skF_2'))), inference(resolution, [status(thm)], [c_12, c_638])).
% 7.93/2.69  tff(c_1341, plain, (~r1_tarski(k7_relat_1('#skF_4', '#skF_3'), k2_zfmisc_1('#skF_3', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_1339, c_692])).
% 7.93/2.69  tff(c_4286, plain, (~r1_tarski('#skF_3', '#skF_1') | ~v5_relat_1(k7_relat_1('#skF_4', '#skF_3'), '#skF_2')), inference(resolution, [status(thm)], [c_4274, c_1341])).
% 7.93/2.69  tff(c_4318, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1720, c_60, c_4286])).
% 7.93/2.69  tff(c_4320, plain, (m1_subset_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitRight, [status(thm)], [c_613])).
% 7.93/2.69  tff(c_4632, plain, (k1_relset_1('#skF_3', '#skF_2', k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))=k1_relat_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))), inference(resolution, [status(thm)], [c_4320, c_4615])).
% 7.93/2.69  tff(c_5080, plain, (k1_relset_1('#skF_3', '#skF_2', k7_relat_1('#skF_4', '#skF_3'))=k1_relat_1(k7_relat_1('#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_5077, c_5077, c_4632])).
% 7.93/2.69  tff(c_4319, plain, (~v1_funct_2(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_613])).
% 7.93/2.69  tff(c_5086, plain, (~v1_funct_2(k7_relat_1('#skF_4', '#skF_3'), '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_5077, c_4319])).
% 7.93/2.69  tff(c_5085, plain, (m1_subset_1(k7_relat_1('#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_5077, c_4320])).
% 7.93/2.69  tff(c_38, plain, (![B_24, C_25, A_23]: (k1_xboole_0=B_24 | v1_funct_2(C_25, A_23, B_24) | k1_relset_1(A_23, B_24, C_25)!=A_23 | ~m1_subset_1(C_25, k1_zfmisc_1(k2_zfmisc_1(A_23, B_24))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 7.93/2.69  tff(c_5147, plain, (k1_xboole_0='#skF_2' | v1_funct_2(k7_relat_1('#skF_4', '#skF_3'), '#skF_3', '#skF_2') | k1_relset_1('#skF_3', '#skF_2', k7_relat_1('#skF_4', '#skF_3'))!='#skF_3'), inference(resolution, [status(thm)], [c_5085, c_38])).
% 7.93/2.69  tff(c_5169, plain, (k1_relset_1('#skF_3', '#skF_2', k7_relat_1('#skF_4', '#skF_3'))!='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_5086, c_71, c_5147])).
% 7.93/2.69  tff(c_5188, plain, (k1_relat_1(k7_relat_1('#skF_4', '#skF_3'))!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_5080, c_5169])).
% 7.93/2.69  tff(c_5262, plain, (~r1_tarski('#skF_3', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_5256, c_5188])).
% 7.93/2.69  tff(c_5287, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_60, c_5262])).
% 7.93/2.69  tff(c_5288, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_58])).
% 7.93/2.69  tff(c_6, plain, (![A_2]: (k2_zfmisc_1(A_2, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 7.93/2.69  tff(c_5301, plain, (![A_2]: (k2_zfmisc_1(A_2, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_5288, c_5288, c_6])).
% 7.93/2.69  tff(c_5289, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_58])).
% 7.93/2.69  tff(c_5294, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_5288, c_5289])).
% 7.93/2.69  tff(c_5341, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_5301, c_5294, c_62])).
% 7.93/2.69  tff(c_5368, plain, (![A_653, B_654]: (r1_tarski(A_653, B_654) | ~m1_subset_1(A_653, k1_zfmisc_1(B_654)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 7.93/2.69  tff(c_5376, plain, (r1_tarski('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_5341, c_5368])).
% 7.93/2.69  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~r1_tarski(A_1, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_29])).
% 7.93/2.69  tff(c_5330, plain, (![A_1]: (A_1='#skF_1' | ~r1_tarski(A_1, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_5288, c_5288, c_2])).
% 7.93/2.69  tff(c_5391, plain, ('#skF_1'='#skF_4'), inference(resolution, [status(thm)], [c_5376, c_5330])).
% 7.93/2.69  tff(c_5295, plain, (v1_funct_2('#skF_4', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_5294, c_64])).
% 7.93/2.69  tff(c_5398, plain, (v1_funct_2('#skF_4', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_5391, c_5391, c_5295])).
% 7.93/2.69  tff(c_5395, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_5391, c_5341])).
% 7.93/2.69  tff(c_8, plain, (![B_3]: (k2_zfmisc_1(k1_xboole_0, B_3)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 7.93/2.69  tff(c_5311, plain, (![B_3]: (k2_zfmisc_1('#skF_1', B_3)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_5288, c_5288, c_8])).
% 7.93/2.69  tff(c_5399, plain, (![B_3]: (k2_zfmisc_1('#skF_4', B_3)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_5391, c_5391, c_5311])).
% 7.93/2.69  tff(c_6304, plain, (![C_791, B_792, A_793]: (v5_relat_1(C_791, B_792) | ~m1_subset_1(C_791, k1_zfmisc_1(k2_zfmisc_1(A_793, B_792))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 7.93/2.69  tff(c_6379, plain, (![C_799, B_800]: (v5_relat_1(C_799, B_800) | ~m1_subset_1(C_799, k1_zfmisc_1('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_5399, c_6304])).
% 7.93/2.69  tff(c_6385, plain, (![B_800]: (v5_relat_1('#skF_4', B_800))), inference(resolution, [status(thm)], [c_5395, c_6379])).
% 7.93/2.69  tff(c_5302, plain, (![A_645]: (k2_zfmisc_1(A_645, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_5288, c_5288, c_6])).
% 7.93/2.69  tff(c_5306, plain, (v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_5302, c_20])).
% 7.93/2.69  tff(c_5347, plain, (![B_648, A_649]: (r1_tarski(k7_relat_1(B_648, A_649), B_648) | ~v1_relat_1(B_648))), inference(cnfTransformation, [status(thm)], [f_58])).
% 7.93/2.69  tff(c_5351, plain, (![A_649]: (k7_relat_1('#skF_1', A_649)='#skF_1' | ~v1_relat_1('#skF_1'))), inference(resolution, [status(thm)], [c_5347, c_5330])).
% 7.93/2.69  tff(c_5354, plain, (![A_649]: (k7_relat_1('#skF_1', A_649)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_5306, c_5351])).
% 7.93/2.69  tff(c_5393, plain, (![A_649]: (k7_relat_1('#skF_4', A_649)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_5391, c_5391, c_5354])).
% 7.93/2.69  tff(c_5401, plain, (![A_2]: (k2_zfmisc_1(A_2, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_5391, c_5391, c_5301])).
% 7.93/2.69  tff(c_7805, plain, (![A_949, B_950, C_951, D_952]: (k2_partfun1(A_949, B_950, C_951, D_952)=k7_relat_1(C_951, D_952) | ~m1_subset_1(C_951, k1_zfmisc_1(k2_zfmisc_1(A_949, B_950))) | ~v1_funct_1(C_951))), inference(cnfTransformation, [status(thm)], [f_106])).
% 7.93/2.69  tff(c_8583, plain, (![A_1014, C_1015, D_1016]: (k2_partfun1(A_1014, '#skF_4', C_1015, D_1016)=k7_relat_1(C_1015, D_1016) | ~m1_subset_1(C_1015, k1_zfmisc_1('#skF_4')) | ~v1_funct_1(C_1015))), inference(superposition, [status(thm), theory('equality')], [c_5401, c_7805])).
% 7.93/2.69  tff(c_8587, plain, (![A_1014, D_1016]: (k2_partfun1(A_1014, '#skF_4', '#skF_4', D_1016)=k7_relat_1('#skF_4', D_1016) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_5395, c_8583])).
% 7.93/2.69  tff(c_8594, plain, (![A_1014, D_1016]: (k2_partfun1(A_1014, '#skF_4', '#skF_4', D_1016)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_5393, c_8587])).
% 7.93/2.69  tff(c_5377, plain, (![B_655, A_656]: (v1_relat_1(B_655) | ~m1_subset_1(B_655, k1_zfmisc_1(A_656)) | ~v1_relat_1(A_656))), inference(cnfTransformation, [status(thm)], [f_46])).
% 7.93/2.69  tff(c_5383, plain, (v1_relat_1('#skF_4') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_5341, c_5377])).
% 7.93/2.69  tff(c_5387, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_5306, c_5383])).
% 7.93/2.69  tff(c_8208, plain, (![B_984, C_985, D_986]: (k2_partfun1('#skF_4', B_984, C_985, D_986)=k7_relat_1(C_985, D_986) | ~m1_subset_1(C_985, k1_zfmisc_1('#skF_4')) | ~v1_funct_1(C_985))), inference(superposition, [status(thm), theory('equality')], [c_5399, c_7805])).
% 7.93/2.69  tff(c_8212, plain, (![B_984, D_986]: (k2_partfun1('#skF_4', B_984, '#skF_4', D_986)=k7_relat_1('#skF_4', D_986) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_5395, c_8208])).
% 7.93/2.69  tff(c_8219, plain, (![B_984, D_986]: (k2_partfun1('#skF_4', B_984, '#skF_4', D_986)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_5393, c_8212])).
% 7.93/2.69  tff(c_6316, plain, (![C_794]: (v5_relat_1(C_794, '#skF_4') | ~m1_subset_1(C_794, k1_zfmisc_1('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_5401, c_6304])).
% 7.93/2.69  tff(c_6324, plain, (v5_relat_1('#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_5395, c_6316])).
% 7.93/2.69  tff(c_6279, plain, (![B_786, A_787]: (r1_tarski(k2_relat_1(B_786), A_787) | ~v5_relat_1(B_786, A_787) | ~v1_relat_1(B_786))), inference(cnfTransformation, [status(thm)], [f_52])).
% 7.93/2.69  tff(c_5397, plain, (![A_1]: (A_1='#skF_4' | ~r1_tarski(A_1, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_5391, c_5391, c_5330])).
% 7.93/2.69  tff(c_6293, plain, (![B_786]: (k2_relat_1(B_786)='#skF_4' | ~v5_relat_1(B_786, '#skF_4') | ~v1_relat_1(B_786))), inference(resolution, [status(thm)], [c_6279, c_5397])).
% 7.93/2.69  tff(c_6328, plain, (k2_relat_1('#skF_4')='#skF_4' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_6324, c_6293])).
% 7.93/2.69  tff(c_6331, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_5387, c_6328])).
% 7.93/2.69  tff(c_6338, plain, (![A_9]: (r1_tarski('#skF_4', A_9) | ~v5_relat_1('#skF_4', A_9) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_6331, c_18])).
% 7.93/2.69  tff(c_6344, plain, (![A_9]: (r1_tarski('#skF_4', A_9) | ~v5_relat_1('#skF_4', A_9))), inference(demodulation, [status(thm), theory('equality')], [c_5387, c_6338])).
% 7.93/2.69  tff(c_6388, plain, (![A_9]: (r1_tarski('#skF_4', A_9))), inference(demodulation, [status(thm), theory('equality')], [c_6385, c_6344])).
% 7.93/2.69  tff(c_7468, plain, (![A_903, B_904, C_905, D_906]: (v1_funct_1(k2_partfun1(A_903, B_904, C_905, D_906)) | ~m1_subset_1(C_905, k1_zfmisc_1(k2_zfmisc_1(A_903, B_904))) | ~v1_funct_1(C_905))), inference(cnfTransformation, [status(thm)], [f_100])).
% 7.93/2.69  tff(c_7514, plain, (![A_925, B_926, A_927, D_928]: (v1_funct_1(k2_partfun1(A_925, B_926, A_927, D_928)) | ~v1_funct_1(A_927) | ~r1_tarski(A_927, k2_zfmisc_1(A_925, B_926)))), inference(resolution, [status(thm)], [c_12, c_7468])).
% 7.93/2.69  tff(c_7517, plain, (![A_925, B_926, D_928]: (v1_funct_1(k2_partfun1(A_925, B_926, '#skF_4', D_928)) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_6388, c_7514])).
% 7.93/2.69  tff(c_7530, plain, (![A_925, B_926, D_928]: (v1_funct_1(k2_partfun1(A_925, B_926, '#skF_4', D_928)))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_7517])).
% 7.93/2.69  tff(c_7538, plain, (![B_932, A_933]: (m1_subset_1(B_932, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_932), A_933))) | ~r1_tarski(k2_relat_1(B_932), A_933) | ~v1_funct_1(B_932) | ~v1_relat_1(B_932))), inference(cnfTransformation, [status(thm)], [f_118])).
% 7.93/2.69  tff(c_7625, plain, (![B_938]: (m1_subset_1(B_938, k1_zfmisc_1('#skF_4')) | ~r1_tarski(k2_relat_1(B_938), '#skF_4') | ~v1_funct_1(B_938) | ~v1_relat_1(B_938))), inference(superposition, [status(thm), theory('equality')], [c_5401, c_7538])).
% 7.93/2.69  tff(c_7656, plain, (![B_941]: (m1_subset_1(B_941, k1_zfmisc_1('#skF_4')) | ~v1_funct_1(B_941) | ~v5_relat_1(B_941, '#skF_4') | ~v1_relat_1(B_941))), inference(resolution, [status(thm)], [c_18, c_7625])).
% 7.93/2.69  tff(c_5402, plain, ('#skF_2'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_5391, c_5294])).
% 7.93/2.69  tff(c_5331, plain, (![A_647]: (A_647='#skF_1' | ~r1_tarski(A_647, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_5288, c_5288, c_2])).
% 7.93/2.69  tff(c_5335, plain, ('#skF_3'='#skF_1'), inference(resolution, [status(thm)], [c_60, c_5331])).
% 7.93/2.69  tff(c_5396, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_5391, c_5335])).
% 7.93/2.69  tff(c_6101, plain, (![A_755, B_756, C_757, D_758]: (v1_funct_1(k2_partfun1(A_755, B_756, C_757, D_758)) | ~m1_subset_1(C_757, k1_zfmisc_1(k2_zfmisc_1(A_755, B_756))) | ~v1_funct_1(C_757))), inference(cnfTransformation, [status(thm)], [f_100])).
% 7.93/2.69  tff(c_6110, plain, (![A_759, C_760, D_761]: (v1_funct_1(k2_partfun1(A_759, '#skF_4', C_760, D_761)) | ~m1_subset_1(C_760, k1_zfmisc_1('#skF_4')) | ~v1_funct_1(C_760))), inference(superposition, [status(thm), theory('equality')], [c_5401, c_6101])).
% 7.93/2.70  tff(c_6112, plain, (![A_759, D_761]: (v1_funct_1(k2_partfun1(A_759, '#skF_4', '#skF_4', D_761)) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_5395, c_6110])).
% 7.93/2.70  tff(c_6118, plain, (![A_759, D_761]: (v1_funct_1(k2_partfun1(A_759, '#skF_4', '#skF_4', D_761)))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_6112])).
% 7.93/2.70  tff(c_5409, plain, (~m1_subset_1(k2_partfun1('#skF_4', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_2(k2_partfun1('#skF_4', '#skF_2', '#skF_4', '#skF_3'), '#skF_3', '#skF_2') | ~v1_funct_1(k2_partfun1('#skF_4', '#skF_2', '#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_5391, c_5391, c_5391, c_56])).
% 7.93/2.70  tff(c_5410, plain, (~v1_funct_1(k2_partfun1('#skF_4', '#skF_2', '#skF_4', '#skF_3'))), inference(splitLeft, [status(thm)], [c_5409])).
% 7.93/2.70  tff(c_5500, plain, (~v1_funct_1(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_5402, c_5396, c_5410])).
% 7.93/2.70  tff(c_6122, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6118, c_5500])).
% 7.93/2.70  tff(c_6123, plain, (~v1_funct_2(k2_partfun1('#skF_4', '#skF_2', '#skF_4', '#skF_3'), '#skF_3', '#skF_2') | ~m1_subset_1(k2_partfun1('#skF_4', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitRight, [status(thm)], [c_5409])).
% 7.93/2.70  tff(c_6252, plain, (~v1_funct_2(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'), '#skF_4', '#skF_4') | ~m1_subset_1(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'), k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_5399, c_5402, c_5402, c_5396, c_5396, c_5402, c_5402, c_5396, c_5396, c_6123])).
% 7.93/2.70  tff(c_6253, plain, (~m1_subset_1(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'), k1_zfmisc_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_6252])).
% 7.93/2.70  tff(c_7671, plain, (~v1_funct_1(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4')) | ~v5_relat_1(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'), '#skF_4') | ~v1_relat_1(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'))), inference(resolution, [status(thm)], [c_7656, c_6253])).
% 7.93/2.70  tff(c_7688, plain, (~v5_relat_1(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'), '#skF_4') | ~v1_relat_1(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_7530, c_7671])).
% 7.93/2.70  tff(c_7875, plain, (~v1_relat_1(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'))), inference(splitLeft, [status(thm)], [c_7688])).
% 7.93/2.70  tff(c_8221, plain, (~v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_8219, c_7875])).
% 7.93/2.70  tff(c_8226, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5387, c_8221])).
% 7.93/2.70  tff(c_8227, plain, (~v5_relat_1(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'), '#skF_4')), inference(splitRight, [status(thm)], [c_7688])).
% 7.93/2.70  tff(c_8596, plain, (~v5_relat_1('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_8594, c_8227])).
% 7.93/2.70  tff(c_8602, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6385, c_8596])).
% 7.93/2.70  tff(c_8604, plain, (m1_subset_1(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'), k1_zfmisc_1('#skF_4'))), inference(splitRight, [status(thm)], [c_6252])).
% 7.93/2.70  tff(c_8722, plain, (r1_tarski(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'), '#skF_4')), inference(resolution, [status(thm)], [c_8604, c_10])).
% 7.93/2.70  tff(c_8732, plain, (k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_8722, c_5397])).
% 7.93/2.70  tff(c_8603, plain, (~v1_funct_2(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'), '#skF_4', '#skF_4')), inference(splitRight, [status(thm)], [c_6252])).
% 7.93/2.70  tff(c_8738, plain, (~v1_funct_2('#skF_4', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_8732, c_8603])).
% 7.93/2.70  tff(c_8746, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5398, c_8738])).
% 7.93/2.70  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.93/2.70  
% 7.93/2.70  Inference rules
% 7.93/2.70  ----------------------
% 7.93/2.70  #Ref     : 0
% 7.93/2.70  #Sup     : 1825
% 7.93/2.70  #Fact    : 0
% 7.93/2.70  #Define  : 0
% 7.93/2.70  #Split   : 24
% 7.93/2.70  #Chain   : 0
% 7.93/2.70  #Close   : 0
% 7.93/2.70  
% 7.93/2.70  Ordering : KBO
% 7.93/2.70  
% 7.93/2.70  Simplification rules
% 7.93/2.70  ----------------------
% 7.93/2.70  #Subsume      : 444
% 7.93/2.70  #Demod        : 1788
% 7.93/2.70  #Tautology    : 704
% 7.93/2.70  #SimpNegUnit  : 86
% 7.93/2.70  #BackRed      : 89
% 7.93/2.70  
% 7.93/2.70  #Partial instantiations: 0
% 7.93/2.70  #Strategies tried      : 1
% 7.93/2.70  
% 7.93/2.70  Timing (in seconds)
% 7.93/2.70  ----------------------
% 7.93/2.70  Preprocessing        : 0.33
% 7.93/2.70  Parsing              : 0.17
% 7.93/2.70  CNF conversion       : 0.02
% 7.93/2.70  Main loop            : 1.51
% 7.93/2.70  Inferencing          : 0.54
% 7.93/2.70  Reduction            : 0.50
% 7.93/2.70  Demodulation         : 0.36
% 7.93/2.70  BG Simplification    : 0.05
% 7.93/2.70  Subsumption          : 0.30
% 7.93/2.70  Abstraction          : 0.06
% 7.93/2.70  MUC search           : 0.00
% 7.93/2.70  Cooper               : 0.00
% 7.93/2.70  Total                : 1.90
% 7.93/2.70  Index Insertion      : 0.00
% 7.93/2.70  Index Deletion       : 0.00
% 7.93/2.70  Index Matching       : 0.00
% 7.93/2.70  BG Taut test         : 0.00
%------------------------------------------------------------------------------
