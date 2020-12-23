%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:37 EST 2020

% Result     : Theorem 4.13s
% Output     : CNFRefutation 4.13s
% Verified   : 
% Statistics : Number of formulae       :  162 (1325 expanded)
%              Number of leaves         :   37 ( 428 expanded)
%              Depth                    :   15
%              Number of atoms          :  267 (4404 expanded)
%              Number of equality atoms :   76 (1640 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   2 average)

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

tff(f_135,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_funct_2)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_61,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => k1_relat_1(k7_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_relat_1)).

tff(f_115,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).

tff(f_109,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( v1_funct_1(k2_partfun1(A,B,C,D))
        & m1_subset_1(k2_partfun1(A,B,C,D),k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_partfun1)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_83,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_29,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

tff(c_54,plain,(
    r1_tarski('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_56,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_90,plain,(
    ! [C_42,A_43,B_44] :
      ( v1_relat_1(C_42)
      | ~ m1_subset_1(C_42,k1_zfmisc_1(k2_zfmisc_1(A_43,B_44))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_98,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_56,c_90])).

tff(c_52,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_65,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_58,plain,(
    v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_880,plain,(
    ! [A_197,B_198,C_199] :
      ( k1_relset_1(A_197,B_198,C_199) = k1_relat_1(C_199)
      | ~ m1_subset_1(C_199,k1_zfmisc_1(k2_zfmisc_1(A_197,B_198))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_894,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_56,c_880])).

tff(c_1142,plain,(
    ! [B_247,A_248,C_249] :
      ( k1_xboole_0 = B_247
      | k1_relset_1(A_248,B_247,C_249) = A_248
      | ~ v1_funct_2(C_249,A_248,B_247)
      | ~ m1_subset_1(C_249,k1_zfmisc_1(k2_zfmisc_1(A_248,B_247))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_1151,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_56,c_1142])).

tff(c_1164,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_894,c_1151])).

tff(c_1165,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_65,c_1164])).

tff(c_20,plain,(
    ! [B_13,A_12] :
      ( k1_relat_1(k7_relat_1(B_13,A_12)) = A_12
      | ~ r1_tarski(A_12,k1_relat_1(B_13))
      | ~ v1_relat_1(B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_1176,plain,(
    ! [A_12] :
      ( k1_relat_1(k7_relat_1('#skF_4',A_12)) = A_12
      | ~ r1_tarski(A_12,'#skF_1')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1165,c_20])).

tff(c_1190,plain,(
    ! [A_250] :
      ( k1_relat_1(k7_relat_1('#skF_4',A_250)) = A_250
      | ~ r1_tarski(A_250,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_1176])).

tff(c_60,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_1015,plain,(
    ! [A_237,B_238,C_239,D_240] :
      ( k2_partfun1(A_237,B_238,C_239,D_240) = k7_relat_1(C_239,D_240)
      | ~ m1_subset_1(C_239,k1_zfmisc_1(k2_zfmisc_1(A_237,B_238)))
      | ~ v1_funct_1(C_239) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_1021,plain,(
    ! [D_240] :
      ( k2_partfun1('#skF_1','#skF_2','#skF_4',D_240) = k7_relat_1('#skF_4',D_240)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_56,c_1015])).

tff(c_1032,plain,(
    ! [D_240] : k2_partfun1('#skF_1','#skF_2','#skF_4',D_240) = k7_relat_1('#skF_4',D_240) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_1021])).

tff(c_18,plain,(
    ! [B_11,A_10] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_11,A_10)),A_10)
      | ~ v1_relat_1(B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_431,plain,(
    ! [A_146,B_147,C_148,D_149] :
      ( k2_partfun1(A_146,B_147,C_148,D_149) = k7_relat_1(C_148,D_149)
      | ~ m1_subset_1(C_148,k1_zfmisc_1(k2_zfmisc_1(A_146,B_147)))
      | ~ v1_funct_1(C_148) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_435,plain,(
    ! [D_149] :
      ( k2_partfun1('#skF_1','#skF_2','#skF_4',D_149) = k7_relat_1('#skF_4',D_149)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_56,c_431])).

tff(c_443,plain,(
    ! [D_149] : k2_partfun1('#skF_1','#skF_2','#skF_4',D_149) = k7_relat_1('#skF_4',D_149) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_435])).

tff(c_684,plain,(
    ! [A_178,B_179,C_180,D_181] :
      ( m1_subset_1(k2_partfun1(A_178,B_179,C_180,D_181),k1_zfmisc_1(k2_zfmisc_1(A_178,B_179)))
      | ~ m1_subset_1(C_180,k1_zfmisc_1(k2_zfmisc_1(A_178,B_179)))
      | ~ v1_funct_1(C_180) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_709,plain,(
    ! [D_149] :
      ( m1_subset_1(k7_relat_1('#skF_4',D_149),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_443,c_684])).

tff(c_734,plain,(
    ! [D_183] : m1_subset_1(k7_relat_1('#skF_4',D_183),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_56,c_709])).

tff(c_24,plain,(
    ! [C_19,B_18,A_17] :
      ( v5_relat_1(C_19,B_18)
      | ~ m1_subset_1(C_19,k1_zfmisc_1(k2_zfmisc_1(A_17,B_18))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_773,plain,(
    ! [D_183] : v5_relat_1(k7_relat_1('#skF_4',D_183),'#skF_2') ),
    inference(resolution,[status(thm)],[c_734,c_24])).

tff(c_14,plain,(
    ! [A_6,B_7] :
      ( v1_relat_1(k7_relat_1(A_6,B_7))
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_366,plain,(
    ! [C_130,A_131,B_132] :
      ( m1_subset_1(C_130,k1_zfmisc_1(k2_zfmisc_1(A_131,B_132)))
      | ~ r1_tarski(k2_relat_1(C_130),B_132)
      | ~ r1_tarski(k1_relat_1(C_130),A_131)
      | ~ v1_relat_1(C_130) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_239,plain,(
    ! [A_85,B_86,C_87,D_88] :
      ( v1_funct_1(k2_partfun1(A_85,B_86,C_87,D_88))
      | ~ m1_subset_1(C_87,k1_zfmisc_1(k2_zfmisc_1(A_85,B_86)))
      | ~ v1_funct_1(C_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_241,plain,(
    ! [D_88] :
      ( v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4',D_88))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_56,c_239])).

tff(c_248,plain,(
    ! [D_88] : v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4',D_88)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_241])).

tff(c_50,plain,
    ( ~ m1_subset_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_2(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_3','#skF_2')
    | ~ v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_140,plain,(
    ~ v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_251,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_248,c_140])).

tff(c_252,plain,
    ( ~ v1_funct_2(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_3','#skF_2')
    | ~ m1_subset_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_304,plain,(
    ~ m1_subset_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_252])).

tff(c_392,plain,
    ( ~ r1_tarski(k2_relat_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')),'#skF_2')
    | ~ r1_tarski(k1_relat_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')),'#skF_3')
    | ~ v1_relat_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')) ),
    inference(resolution,[status(thm)],[c_366,c_304])).

tff(c_529,plain,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_4','#skF_3')),'#skF_2')
    | ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_4','#skF_3')),'#skF_3')
    | ~ v1_relat_1(k7_relat_1('#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_443,c_443,c_443,c_392])).

tff(c_530,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_4','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_529])).

tff(c_533,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_14,c_530])).

tff(c_537,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_533])).

tff(c_539,plain,(
    v1_relat_1(k7_relat_1('#skF_4','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_529])).

tff(c_12,plain,(
    ! [B_5,A_4] :
      ( r1_tarski(k2_relat_1(B_5),A_4)
      | ~ v5_relat_1(B_5,A_4)
      | ~ v1_relat_1(B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_538,plain,
    ( ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_4','#skF_3')),'#skF_3')
    | ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_4','#skF_3')),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_529])).

tff(c_540,plain,(
    ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_4','#skF_3')),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_538])).

tff(c_543,plain,
    ( ~ v5_relat_1(k7_relat_1('#skF_4','#skF_3'),'#skF_2')
    | ~ v1_relat_1(k7_relat_1('#skF_4','#skF_3')) ),
    inference(resolution,[status(thm)],[c_12,c_540])).

tff(c_546,plain,(
    ~ v5_relat_1(k7_relat_1('#skF_4','#skF_3'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_539,c_543])).

tff(c_799,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_773,c_546])).

tff(c_800,plain,(
    ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_4','#skF_3')),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_538])).

tff(c_826,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_18,c_800])).

tff(c_830,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_826])).

tff(c_832,plain,(
    m1_subset_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_252])).

tff(c_893,plain,(
    k1_relset_1('#skF_3','#skF_2',k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')) = k1_relat_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')) ),
    inference(resolution,[status(thm)],[c_832,c_880])).

tff(c_1034,plain,(
    k1_relset_1('#skF_3','#skF_2',k7_relat_1('#skF_4','#skF_3')) = k1_relat_1(k7_relat_1('#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1032,c_1032,c_893])).

tff(c_831,plain,(
    ~ v1_funct_2(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_252])).

tff(c_1042,plain,(
    ~ v1_funct_2(k7_relat_1('#skF_4','#skF_3'),'#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1032,c_831])).

tff(c_1041,plain,(
    m1_subset_1(k7_relat_1('#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1032,c_832])).

tff(c_38,plain,(
    ! [B_27,C_28,A_26] :
      ( k1_xboole_0 = B_27
      | v1_funct_2(C_28,A_26,B_27)
      | k1_relset_1(A_26,B_27,C_28) != A_26
      | ~ m1_subset_1(C_28,k1_zfmisc_1(k2_zfmisc_1(A_26,B_27))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_1087,plain,
    ( k1_xboole_0 = '#skF_2'
    | v1_funct_2(k7_relat_1('#skF_4','#skF_3'),'#skF_3','#skF_2')
    | k1_relset_1('#skF_3','#skF_2',k7_relat_1('#skF_4','#skF_3')) != '#skF_3' ),
    inference(resolution,[status(thm)],[c_1041,c_38])).

tff(c_1106,plain,(
    k1_relset_1('#skF_3','#skF_2',k7_relat_1('#skF_4','#skF_3')) != '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_1042,c_65,c_1087])).

tff(c_1137,plain,(
    k1_relat_1(k7_relat_1('#skF_4','#skF_3')) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1034,c_1106])).

tff(c_1196,plain,(
    ~ r1_tarski('#skF_3','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1190,c_1137])).

tff(c_1236,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_1196])).

tff(c_1237,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_6,plain,(
    ! [A_2] : k2_zfmisc_1(A_2,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1249,plain,(
    ! [A_2] : k2_zfmisc_1(A_2,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1237,c_1237,c_6])).

tff(c_1238,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_1243,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1237,c_1238])).

tff(c_1289,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1249,c_1243,c_56])).

tff(c_8,plain,(
    ! [B_3] : k2_zfmisc_1(k1_xboole_0,B_3) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1257,plain,(
    ! [B_3] : k2_zfmisc_1('#skF_1',B_3) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1237,c_1237,c_8])).

tff(c_1291,plain,(
    ! [C_256,A_257,B_258] :
      ( v1_relat_1(C_256)
      | ~ m1_subset_1(C_256,k1_zfmisc_1(k2_zfmisc_1(A_257,B_258))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_1296,plain,(
    ! [C_259] :
      ( v1_relat_1(C_259)
      | ~ m1_subset_1(C_259,k1_zfmisc_1('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1257,c_1291])).

tff(c_1300,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_1289,c_1296])).

tff(c_1624,plain,(
    ! [C_323,A_324,B_325] :
      ( v4_relat_1(C_323,A_324)
      | ~ m1_subset_1(C_323,k1_zfmisc_1(k2_zfmisc_1(A_324,B_325))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_1674,plain,(
    ! [C_328,A_329] :
      ( v4_relat_1(C_328,A_329)
      | ~ m1_subset_1(C_328,k1_zfmisc_1('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1249,c_1624])).

tff(c_1679,plain,(
    ! [A_330] : v4_relat_1('#skF_4',A_330) ),
    inference(resolution,[status(thm)],[c_1289,c_1674])).

tff(c_16,plain,(
    ! [B_9,A_8] :
      ( k7_relat_1(B_9,A_8) = B_9
      | ~ v4_relat_1(B_9,A_8)
      | ~ v1_relat_1(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1682,plain,(
    ! [A_330] :
      ( k7_relat_1('#skF_4',A_330) = '#skF_4'
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_1679,c_16])).

tff(c_1685,plain,(
    ! [A_330] : k7_relat_1('#skF_4',A_330) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1300,c_1682])).

tff(c_1887,plain,(
    ! [A_369,B_370,C_371,D_372] :
      ( k2_partfun1(A_369,B_370,C_371,D_372) = k7_relat_1(C_371,D_372)
      | ~ m1_subset_1(C_371,k1_zfmisc_1(k2_zfmisc_1(A_369,B_370)))
      | ~ v1_funct_1(C_371) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_1898,plain,(
    ! [B_374,C_375,D_376] :
      ( k2_partfun1('#skF_1',B_374,C_375,D_376) = k7_relat_1(C_375,D_376)
      | ~ m1_subset_1(C_375,k1_zfmisc_1('#skF_1'))
      | ~ v1_funct_1(C_375) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1257,c_1887])).

tff(c_1900,plain,(
    ! [B_374,D_376] :
      ( k2_partfun1('#skF_1',B_374,'#skF_4',D_376) = k7_relat_1('#skF_4',D_376)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_1289,c_1898])).

tff(c_1903,plain,(
    ! [B_374,D_376] : k2_partfun1('#skF_1',B_374,'#skF_4',D_376) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_1685,c_1900])).

tff(c_1562,plain,(
    ! [A_305,B_306,C_307,D_308] :
      ( v1_funct_1(k2_partfun1(A_305,B_306,C_307,D_308))
      | ~ m1_subset_1(C_307,k1_zfmisc_1(k2_zfmisc_1(A_305,B_306)))
      | ~ v1_funct_1(C_307) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_1567,plain,(
    ! [B_309,C_310,D_311] :
      ( v1_funct_1(k2_partfun1('#skF_1',B_309,C_310,D_311))
      | ~ m1_subset_1(C_310,k1_zfmisc_1('#skF_1'))
      | ~ v1_funct_1(C_310) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1257,c_1562])).

tff(c_1569,plain,(
    ! [B_309,D_311] :
      ( v1_funct_1(k2_partfun1('#skF_1',B_309,'#skF_4',D_311))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_1289,c_1567])).

tff(c_1572,plain,(
    ! [B_309,D_311] : v1_funct_1(k2_partfun1('#skF_1',B_309,'#skF_4',D_311)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_1569])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ r1_tarski(A_1,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_1274,plain,(
    ! [A_253] :
      ( A_253 = '#skF_1'
      | ~ r1_tarski(A_253,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1237,c_1237,c_2])).

tff(c_1278,plain,(
    '#skF_3' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_54,c_1274])).

tff(c_1333,plain,
    ( ~ m1_subset_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),k1_zfmisc_1('#skF_1'))
    | ~ v1_funct_2(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),'#skF_1','#skF_1')
    | ~ v1_funct_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1278,c_1243,c_1278,c_1278,c_1243,c_1243,c_1278,c_1249,c_1243,c_1243,c_50])).

tff(c_1334,plain,(
    ~ v1_funct_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_1333])).

tff(c_1575,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1572,c_1334])).

tff(c_1576,plain,
    ( ~ v1_funct_2(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),'#skF_1','#skF_1')
    | ~ m1_subset_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),k1_zfmisc_1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_1333])).

tff(c_1590,plain,(
    ~ m1_subset_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),k1_zfmisc_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_1576])).

tff(c_1905,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1903,c_1590])).

tff(c_1909,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1289,c_1905])).

tff(c_1911,plain,(
    m1_subset_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),k1_zfmisc_1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_1576])).

tff(c_1293,plain,(
    ! [C_256] :
      ( v1_relat_1(C_256)
      | ~ m1_subset_1(C_256,k1_zfmisc_1('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1257,c_1291])).

tff(c_1918,plain,(
    v1_relat_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1')) ),
    inference(resolution,[status(thm)],[c_1911,c_1293])).

tff(c_1920,plain,(
    ! [C_378,A_379,B_380] :
      ( v4_relat_1(C_378,A_379)
      | ~ m1_subset_1(C_378,k1_zfmisc_1(k2_zfmisc_1(A_379,B_380))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_1927,plain,(
    ! [C_381] :
      ( v4_relat_1(C_381,'#skF_1')
      | ~ m1_subset_1(C_381,k1_zfmisc_1('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1257,c_1920])).

tff(c_1934,plain,(
    v4_relat_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_1911,c_1927])).

tff(c_1973,plain,
    ( k7_relat_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),'#skF_1') = k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1')
    | ~ v1_relat_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1')) ),
    inference(resolution,[status(thm)],[c_1934,c_16])).

tff(c_1976,plain,(
    k7_relat_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),'#skF_1') = k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1918,c_1973])).

tff(c_1301,plain,(
    ! [B_260,A_261] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_260,A_261)),A_261)
      | ~ v1_relat_1(B_260) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_1273,plain,(
    ! [A_1] :
      ( A_1 = '#skF_1'
      | ~ r1_tarski(A_1,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1237,c_1237,c_2])).

tff(c_1306,plain,(
    ! [B_260] :
      ( k1_relat_1(k7_relat_1(B_260,'#skF_1')) = '#skF_1'
      | ~ v1_relat_1(B_260) ) ),
    inference(resolution,[status(thm)],[c_1301,c_1273])).

tff(c_2170,plain,
    ( k1_relat_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1')) = '#skF_1'
    | ~ v1_relat_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1976,c_1306])).

tff(c_2180,plain,(
    k1_relat_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1918,c_2170])).

tff(c_2107,plain,(
    ! [A_395,B_396,C_397] :
      ( k1_relset_1(A_395,B_396,C_397) = k1_relat_1(C_397)
      | ~ m1_subset_1(C_397,k1_zfmisc_1(k2_zfmisc_1(A_395,B_396))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_2114,plain,(
    ! [B_398,C_399] :
      ( k1_relset_1('#skF_1',B_398,C_399) = k1_relat_1(C_399)
      | ~ m1_subset_1(C_399,k1_zfmisc_1('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1257,c_2107])).

tff(c_2119,plain,(
    ! [B_398] : k1_relset_1('#skF_1',B_398,k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1')) = k1_relat_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1')) ),
    inference(resolution,[status(thm)],[c_1911,c_2114])).

tff(c_2186,plain,(
    ! [B_398] : k1_relset_1('#skF_1',B_398,k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2180,c_2119])).

tff(c_36,plain,(
    ! [C_28,B_27] :
      ( v1_funct_2(C_28,k1_xboole_0,B_27)
      | k1_relset_1(k1_xboole_0,B_27,C_28) != k1_xboole_0
      | ~ m1_subset_1(C_28,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_27))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_62,plain,(
    ! [C_28,B_27] :
      ( v1_funct_2(C_28,k1_xboole_0,B_27)
      | k1_relset_1(k1_xboole_0,B_27,C_28) != k1_xboole_0
      | ~ m1_subset_1(C_28,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_36])).

tff(c_2237,plain,(
    ! [C_411,B_412] :
      ( v1_funct_2(C_411,'#skF_1',B_412)
      | k1_relset_1('#skF_1',B_412,C_411) != '#skF_1'
      | ~ m1_subset_1(C_411,k1_zfmisc_1('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1237,c_1237,c_1237,c_1237,c_62])).

tff(c_2239,plain,(
    ! [B_412] :
      ( v1_funct_2(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),'#skF_1',B_412)
      | k1_relset_1('#skF_1',B_412,k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1')) != '#skF_1' ) ),
    inference(resolution,[status(thm)],[c_1911,c_2237])).

tff(c_2244,plain,(
    ! [B_412] : v1_funct_2(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),'#skF_1',B_412) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2186,c_2239])).

tff(c_1910,plain,(
    ~ v1_funct_2(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),'#skF_1','#skF_1') ),
    inference(splitRight,[status(thm)],[c_1576])).

tff(c_2280,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2244,c_1910])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:01:57 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.13/1.68  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.13/1.71  
% 4.13/1.71  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.13/1.72  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_partfun1 > k1_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 4.13/1.72  
% 4.13/1.72  %Foreground sorts:
% 4.13/1.72  
% 4.13/1.72  
% 4.13/1.72  %Background operators:
% 4.13/1.72  
% 4.13/1.72  
% 4.13/1.72  %Foreground operators:
% 4.13/1.72  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.13/1.72  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.13/1.72  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 4.13/1.72  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.13/1.72  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.13/1.72  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.13/1.72  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.13/1.72  tff('#skF_2', type, '#skF_2': $i).
% 4.13/1.72  tff('#skF_3', type, '#skF_3': $i).
% 4.13/1.72  tff('#skF_1', type, '#skF_1': $i).
% 4.13/1.72  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 4.13/1.72  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 4.13/1.72  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.13/1.72  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.13/1.72  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.13/1.72  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.13/1.72  tff('#skF_4', type, '#skF_4': $i).
% 4.13/1.72  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.13/1.72  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 4.13/1.72  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 4.13/1.72  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.13/1.72  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.13/1.72  
% 4.13/1.74  tff(f_135, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_tarski(C, A) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | ((v1_funct_1(k2_partfun1(A, B, D, C)) & v1_funct_2(k2_partfun1(A, B, D, C), C, B)) & m1_subset_1(k2_partfun1(A, B, D, C), k1_zfmisc_1(k2_zfmisc_1(C, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_funct_2)).
% 4.13/1.74  tff(f_65, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 4.13/1.74  tff(f_75, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 4.13/1.74  tff(f_101, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 4.13/1.74  tff(f_61, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => (k1_relat_1(k7_relat_1(B, A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_relat_1)).
% 4.13/1.74  tff(f_115, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 4.13/1.74  tff(f_55, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_relat_1)).
% 4.13/1.74  tff(f_109, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (v1_funct_1(k2_partfun1(A, B, C, D)) & m1_subset_1(k2_partfun1(A, B, C, D), k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_partfun1)).
% 4.13/1.74  tff(f_71, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 4.13/1.74  tff(f_45, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 4.13/1.74  tff(f_83, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_relset_1)).
% 4.13/1.74  tff(f_41, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 4.13/1.74  tff(f_35, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 4.13/1.74  tff(f_51, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 4.13/1.74  tff(f_29, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_1)).
% 4.13/1.74  tff(c_54, plain, (r1_tarski('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_135])).
% 4.13/1.74  tff(c_56, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_135])).
% 4.13/1.74  tff(c_90, plain, (![C_42, A_43, B_44]: (v1_relat_1(C_42) | ~m1_subset_1(C_42, k1_zfmisc_1(k2_zfmisc_1(A_43, B_44))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.13/1.74  tff(c_98, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_56, c_90])).
% 4.13/1.74  tff(c_52, plain, (k1_xboole_0='#skF_1' | k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_135])).
% 4.13/1.74  tff(c_65, plain, (k1_xboole_0!='#skF_2'), inference(splitLeft, [status(thm)], [c_52])).
% 4.13/1.74  tff(c_58, plain, (v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_135])).
% 4.13/1.74  tff(c_880, plain, (![A_197, B_198, C_199]: (k1_relset_1(A_197, B_198, C_199)=k1_relat_1(C_199) | ~m1_subset_1(C_199, k1_zfmisc_1(k2_zfmisc_1(A_197, B_198))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.13/1.74  tff(c_894, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_56, c_880])).
% 4.13/1.74  tff(c_1142, plain, (![B_247, A_248, C_249]: (k1_xboole_0=B_247 | k1_relset_1(A_248, B_247, C_249)=A_248 | ~v1_funct_2(C_249, A_248, B_247) | ~m1_subset_1(C_249, k1_zfmisc_1(k2_zfmisc_1(A_248, B_247))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 4.13/1.74  tff(c_1151, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_1' | ~v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_56, c_1142])).
% 4.13/1.74  tff(c_1164, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_58, c_894, c_1151])).
% 4.13/1.74  tff(c_1165, plain, (k1_relat_1('#skF_4')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_65, c_1164])).
% 4.13/1.74  tff(c_20, plain, (![B_13, A_12]: (k1_relat_1(k7_relat_1(B_13, A_12))=A_12 | ~r1_tarski(A_12, k1_relat_1(B_13)) | ~v1_relat_1(B_13))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.13/1.74  tff(c_1176, plain, (![A_12]: (k1_relat_1(k7_relat_1('#skF_4', A_12))=A_12 | ~r1_tarski(A_12, '#skF_1') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1165, c_20])).
% 4.13/1.74  tff(c_1190, plain, (![A_250]: (k1_relat_1(k7_relat_1('#skF_4', A_250))=A_250 | ~r1_tarski(A_250, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_1176])).
% 4.13/1.74  tff(c_60, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_135])).
% 4.13/1.74  tff(c_1015, plain, (![A_237, B_238, C_239, D_240]: (k2_partfun1(A_237, B_238, C_239, D_240)=k7_relat_1(C_239, D_240) | ~m1_subset_1(C_239, k1_zfmisc_1(k2_zfmisc_1(A_237, B_238))) | ~v1_funct_1(C_239))), inference(cnfTransformation, [status(thm)], [f_115])).
% 4.13/1.74  tff(c_1021, plain, (![D_240]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_240)=k7_relat_1('#skF_4', D_240) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_56, c_1015])).
% 4.13/1.74  tff(c_1032, plain, (![D_240]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_240)=k7_relat_1('#skF_4', D_240))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_1021])).
% 4.13/1.74  tff(c_18, plain, (![B_11, A_10]: (r1_tarski(k1_relat_1(k7_relat_1(B_11, A_10)), A_10) | ~v1_relat_1(B_11))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.13/1.74  tff(c_431, plain, (![A_146, B_147, C_148, D_149]: (k2_partfun1(A_146, B_147, C_148, D_149)=k7_relat_1(C_148, D_149) | ~m1_subset_1(C_148, k1_zfmisc_1(k2_zfmisc_1(A_146, B_147))) | ~v1_funct_1(C_148))), inference(cnfTransformation, [status(thm)], [f_115])).
% 4.13/1.74  tff(c_435, plain, (![D_149]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_149)=k7_relat_1('#skF_4', D_149) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_56, c_431])).
% 4.13/1.74  tff(c_443, plain, (![D_149]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_149)=k7_relat_1('#skF_4', D_149))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_435])).
% 4.13/1.74  tff(c_684, plain, (![A_178, B_179, C_180, D_181]: (m1_subset_1(k2_partfun1(A_178, B_179, C_180, D_181), k1_zfmisc_1(k2_zfmisc_1(A_178, B_179))) | ~m1_subset_1(C_180, k1_zfmisc_1(k2_zfmisc_1(A_178, B_179))) | ~v1_funct_1(C_180))), inference(cnfTransformation, [status(thm)], [f_109])).
% 4.13/1.74  tff(c_709, plain, (![D_149]: (m1_subset_1(k7_relat_1('#skF_4', D_149), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_443, c_684])).
% 4.13/1.74  tff(c_734, plain, (![D_183]: (m1_subset_1(k7_relat_1('#skF_4', D_183), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_56, c_709])).
% 4.13/1.74  tff(c_24, plain, (![C_19, B_18, A_17]: (v5_relat_1(C_19, B_18) | ~m1_subset_1(C_19, k1_zfmisc_1(k2_zfmisc_1(A_17, B_18))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.13/1.74  tff(c_773, plain, (![D_183]: (v5_relat_1(k7_relat_1('#skF_4', D_183), '#skF_2'))), inference(resolution, [status(thm)], [c_734, c_24])).
% 4.13/1.74  tff(c_14, plain, (![A_6, B_7]: (v1_relat_1(k7_relat_1(A_6, B_7)) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.13/1.74  tff(c_366, plain, (![C_130, A_131, B_132]: (m1_subset_1(C_130, k1_zfmisc_1(k2_zfmisc_1(A_131, B_132))) | ~r1_tarski(k2_relat_1(C_130), B_132) | ~r1_tarski(k1_relat_1(C_130), A_131) | ~v1_relat_1(C_130))), inference(cnfTransformation, [status(thm)], [f_83])).
% 4.13/1.74  tff(c_239, plain, (![A_85, B_86, C_87, D_88]: (v1_funct_1(k2_partfun1(A_85, B_86, C_87, D_88)) | ~m1_subset_1(C_87, k1_zfmisc_1(k2_zfmisc_1(A_85, B_86))) | ~v1_funct_1(C_87))), inference(cnfTransformation, [status(thm)], [f_109])).
% 4.13/1.74  tff(c_241, plain, (![D_88]: (v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_88)) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_56, c_239])).
% 4.13/1.74  tff(c_248, plain, (![D_88]: (v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_88)))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_241])).
% 4.13/1.74  tff(c_50, plain, (~m1_subset_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_2(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_3', '#skF_2') | ~v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_135])).
% 4.13/1.74  tff(c_140, plain, (~v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))), inference(splitLeft, [status(thm)], [c_50])).
% 4.13/1.74  tff(c_251, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_248, c_140])).
% 4.13/1.74  tff(c_252, plain, (~v1_funct_2(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_3', '#skF_2') | ~m1_subset_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitRight, [status(thm)], [c_50])).
% 4.13/1.74  tff(c_304, plain, (~m1_subset_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitLeft, [status(thm)], [c_252])).
% 4.13/1.74  tff(c_392, plain, (~r1_tarski(k2_relat_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3')), '#skF_2') | ~r1_tarski(k1_relat_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3')), '#skF_3') | ~v1_relat_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))), inference(resolution, [status(thm)], [c_366, c_304])).
% 4.13/1.74  tff(c_529, plain, (~r1_tarski(k2_relat_1(k7_relat_1('#skF_4', '#skF_3')), '#skF_2') | ~r1_tarski(k1_relat_1(k7_relat_1('#skF_4', '#skF_3')), '#skF_3') | ~v1_relat_1(k7_relat_1('#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_443, c_443, c_443, c_392])).
% 4.13/1.74  tff(c_530, plain, (~v1_relat_1(k7_relat_1('#skF_4', '#skF_3'))), inference(splitLeft, [status(thm)], [c_529])).
% 4.13/1.74  tff(c_533, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_14, c_530])).
% 4.13/1.74  tff(c_537, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_98, c_533])).
% 4.13/1.74  tff(c_539, plain, (v1_relat_1(k7_relat_1('#skF_4', '#skF_3'))), inference(splitRight, [status(thm)], [c_529])).
% 4.13/1.74  tff(c_12, plain, (![B_5, A_4]: (r1_tarski(k2_relat_1(B_5), A_4) | ~v5_relat_1(B_5, A_4) | ~v1_relat_1(B_5))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.13/1.74  tff(c_538, plain, (~r1_tarski(k1_relat_1(k7_relat_1('#skF_4', '#skF_3')), '#skF_3') | ~r1_tarski(k2_relat_1(k7_relat_1('#skF_4', '#skF_3')), '#skF_2')), inference(splitRight, [status(thm)], [c_529])).
% 4.13/1.74  tff(c_540, plain, (~r1_tarski(k2_relat_1(k7_relat_1('#skF_4', '#skF_3')), '#skF_2')), inference(splitLeft, [status(thm)], [c_538])).
% 4.13/1.74  tff(c_543, plain, (~v5_relat_1(k7_relat_1('#skF_4', '#skF_3'), '#skF_2') | ~v1_relat_1(k7_relat_1('#skF_4', '#skF_3'))), inference(resolution, [status(thm)], [c_12, c_540])).
% 4.13/1.74  tff(c_546, plain, (~v5_relat_1(k7_relat_1('#skF_4', '#skF_3'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_539, c_543])).
% 4.13/1.74  tff(c_799, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_773, c_546])).
% 4.13/1.74  tff(c_800, plain, (~r1_tarski(k1_relat_1(k7_relat_1('#skF_4', '#skF_3')), '#skF_3')), inference(splitRight, [status(thm)], [c_538])).
% 4.13/1.74  tff(c_826, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_18, c_800])).
% 4.13/1.74  tff(c_830, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_98, c_826])).
% 4.13/1.74  tff(c_832, plain, (m1_subset_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitRight, [status(thm)], [c_252])).
% 4.13/1.74  tff(c_893, plain, (k1_relset_1('#skF_3', '#skF_2', k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))=k1_relat_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))), inference(resolution, [status(thm)], [c_832, c_880])).
% 4.13/1.74  tff(c_1034, plain, (k1_relset_1('#skF_3', '#skF_2', k7_relat_1('#skF_4', '#skF_3'))=k1_relat_1(k7_relat_1('#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1032, c_1032, c_893])).
% 4.13/1.74  tff(c_831, plain, (~v1_funct_2(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_252])).
% 4.13/1.74  tff(c_1042, plain, (~v1_funct_2(k7_relat_1('#skF_4', '#skF_3'), '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1032, c_831])).
% 4.13/1.74  tff(c_1041, plain, (m1_subset_1(k7_relat_1('#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_1032, c_832])).
% 4.13/1.74  tff(c_38, plain, (![B_27, C_28, A_26]: (k1_xboole_0=B_27 | v1_funct_2(C_28, A_26, B_27) | k1_relset_1(A_26, B_27, C_28)!=A_26 | ~m1_subset_1(C_28, k1_zfmisc_1(k2_zfmisc_1(A_26, B_27))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 4.13/1.74  tff(c_1087, plain, (k1_xboole_0='#skF_2' | v1_funct_2(k7_relat_1('#skF_4', '#skF_3'), '#skF_3', '#skF_2') | k1_relset_1('#skF_3', '#skF_2', k7_relat_1('#skF_4', '#skF_3'))!='#skF_3'), inference(resolution, [status(thm)], [c_1041, c_38])).
% 4.13/1.74  tff(c_1106, plain, (k1_relset_1('#skF_3', '#skF_2', k7_relat_1('#skF_4', '#skF_3'))!='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_1042, c_65, c_1087])).
% 4.13/1.74  tff(c_1137, plain, (k1_relat_1(k7_relat_1('#skF_4', '#skF_3'))!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1034, c_1106])).
% 4.13/1.74  tff(c_1196, plain, (~r1_tarski('#skF_3', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1190, c_1137])).
% 4.13/1.74  tff(c_1236, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54, c_1196])).
% 4.13/1.74  tff(c_1237, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_52])).
% 4.13/1.74  tff(c_6, plain, (![A_2]: (k2_zfmisc_1(A_2, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.13/1.74  tff(c_1249, plain, (![A_2]: (k2_zfmisc_1(A_2, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1237, c_1237, c_6])).
% 4.13/1.74  tff(c_1238, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_52])).
% 4.13/1.74  tff(c_1243, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1237, c_1238])).
% 4.13/1.74  tff(c_1289, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_1249, c_1243, c_56])).
% 4.13/1.74  tff(c_8, plain, (![B_3]: (k2_zfmisc_1(k1_xboole_0, B_3)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.13/1.74  tff(c_1257, plain, (![B_3]: (k2_zfmisc_1('#skF_1', B_3)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1237, c_1237, c_8])).
% 4.13/1.74  tff(c_1291, plain, (![C_256, A_257, B_258]: (v1_relat_1(C_256) | ~m1_subset_1(C_256, k1_zfmisc_1(k2_zfmisc_1(A_257, B_258))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.13/1.74  tff(c_1296, plain, (![C_259]: (v1_relat_1(C_259) | ~m1_subset_1(C_259, k1_zfmisc_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_1257, c_1291])).
% 4.13/1.74  tff(c_1300, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_1289, c_1296])).
% 4.13/1.74  tff(c_1624, plain, (![C_323, A_324, B_325]: (v4_relat_1(C_323, A_324) | ~m1_subset_1(C_323, k1_zfmisc_1(k2_zfmisc_1(A_324, B_325))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.13/1.74  tff(c_1674, plain, (![C_328, A_329]: (v4_relat_1(C_328, A_329) | ~m1_subset_1(C_328, k1_zfmisc_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_1249, c_1624])).
% 4.13/1.74  tff(c_1679, plain, (![A_330]: (v4_relat_1('#skF_4', A_330))), inference(resolution, [status(thm)], [c_1289, c_1674])).
% 4.13/1.74  tff(c_16, plain, (![B_9, A_8]: (k7_relat_1(B_9, A_8)=B_9 | ~v4_relat_1(B_9, A_8) | ~v1_relat_1(B_9))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.13/1.74  tff(c_1682, plain, (![A_330]: (k7_relat_1('#skF_4', A_330)='#skF_4' | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_1679, c_16])).
% 4.13/1.74  tff(c_1685, plain, (![A_330]: (k7_relat_1('#skF_4', A_330)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1300, c_1682])).
% 4.13/1.74  tff(c_1887, plain, (![A_369, B_370, C_371, D_372]: (k2_partfun1(A_369, B_370, C_371, D_372)=k7_relat_1(C_371, D_372) | ~m1_subset_1(C_371, k1_zfmisc_1(k2_zfmisc_1(A_369, B_370))) | ~v1_funct_1(C_371))), inference(cnfTransformation, [status(thm)], [f_115])).
% 4.13/1.74  tff(c_1898, plain, (![B_374, C_375, D_376]: (k2_partfun1('#skF_1', B_374, C_375, D_376)=k7_relat_1(C_375, D_376) | ~m1_subset_1(C_375, k1_zfmisc_1('#skF_1')) | ~v1_funct_1(C_375))), inference(superposition, [status(thm), theory('equality')], [c_1257, c_1887])).
% 4.13/1.74  tff(c_1900, plain, (![B_374, D_376]: (k2_partfun1('#skF_1', B_374, '#skF_4', D_376)=k7_relat_1('#skF_4', D_376) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_1289, c_1898])).
% 4.13/1.74  tff(c_1903, plain, (![B_374, D_376]: (k2_partfun1('#skF_1', B_374, '#skF_4', D_376)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_1685, c_1900])).
% 4.13/1.74  tff(c_1562, plain, (![A_305, B_306, C_307, D_308]: (v1_funct_1(k2_partfun1(A_305, B_306, C_307, D_308)) | ~m1_subset_1(C_307, k1_zfmisc_1(k2_zfmisc_1(A_305, B_306))) | ~v1_funct_1(C_307))), inference(cnfTransformation, [status(thm)], [f_109])).
% 4.13/1.74  tff(c_1567, plain, (![B_309, C_310, D_311]: (v1_funct_1(k2_partfun1('#skF_1', B_309, C_310, D_311)) | ~m1_subset_1(C_310, k1_zfmisc_1('#skF_1')) | ~v1_funct_1(C_310))), inference(superposition, [status(thm), theory('equality')], [c_1257, c_1562])).
% 4.13/1.74  tff(c_1569, plain, (![B_309, D_311]: (v1_funct_1(k2_partfun1('#skF_1', B_309, '#skF_4', D_311)) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_1289, c_1567])).
% 4.13/1.74  tff(c_1572, plain, (![B_309, D_311]: (v1_funct_1(k2_partfun1('#skF_1', B_309, '#skF_4', D_311)))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_1569])).
% 4.13/1.74  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~r1_tarski(A_1, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.13/1.74  tff(c_1274, plain, (![A_253]: (A_253='#skF_1' | ~r1_tarski(A_253, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_1237, c_1237, c_2])).
% 4.13/1.74  tff(c_1278, plain, ('#skF_3'='#skF_1'), inference(resolution, [status(thm)], [c_54, c_1274])).
% 4.13/1.74  tff(c_1333, plain, (~m1_subset_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), k1_zfmisc_1('#skF_1')) | ~v1_funct_2(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), '#skF_1', '#skF_1') | ~v1_funct_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_1278, c_1243, c_1278, c_1278, c_1243, c_1243, c_1278, c_1249, c_1243, c_1243, c_50])).
% 4.13/1.74  tff(c_1334, plain, (~v1_funct_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'))), inference(splitLeft, [status(thm)], [c_1333])).
% 4.13/1.74  tff(c_1575, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1572, c_1334])).
% 4.13/1.74  tff(c_1576, plain, (~v1_funct_2(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), '#skF_1', '#skF_1') | ~m1_subset_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), k1_zfmisc_1('#skF_1'))), inference(splitRight, [status(thm)], [c_1333])).
% 4.13/1.74  tff(c_1590, plain, (~m1_subset_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), k1_zfmisc_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_1576])).
% 4.13/1.74  tff(c_1905, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_1903, c_1590])).
% 4.13/1.74  tff(c_1909, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1289, c_1905])).
% 4.13/1.74  tff(c_1911, plain, (m1_subset_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), k1_zfmisc_1('#skF_1'))), inference(splitRight, [status(thm)], [c_1576])).
% 4.13/1.74  tff(c_1293, plain, (![C_256]: (v1_relat_1(C_256) | ~m1_subset_1(C_256, k1_zfmisc_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_1257, c_1291])).
% 4.13/1.74  tff(c_1918, plain, (v1_relat_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'))), inference(resolution, [status(thm)], [c_1911, c_1293])).
% 4.13/1.74  tff(c_1920, plain, (![C_378, A_379, B_380]: (v4_relat_1(C_378, A_379) | ~m1_subset_1(C_378, k1_zfmisc_1(k2_zfmisc_1(A_379, B_380))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.13/1.74  tff(c_1927, plain, (![C_381]: (v4_relat_1(C_381, '#skF_1') | ~m1_subset_1(C_381, k1_zfmisc_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_1257, c_1920])).
% 4.13/1.74  tff(c_1934, plain, (v4_relat_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), '#skF_1')), inference(resolution, [status(thm)], [c_1911, c_1927])).
% 4.13/1.74  tff(c_1973, plain, (k7_relat_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), '#skF_1')=k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1') | ~v1_relat_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'))), inference(resolution, [status(thm)], [c_1934, c_16])).
% 4.13/1.74  tff(c_1976, plain, (k7_relat_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), '#skF_1')=k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1918, c_1973])).
% 4.13/1.74  tff(c_1301, plain, (![B_260, A_261]: (r1_tarski(k1_relat_1(k7_relat_1(B_260, A_261)), A_261) | ~v1_relat_1(B_260))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.13/1.74  tff(c_1273, plain, (![A_1]: (A_1='#skF_1' | ~r1_tarski(A_1, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_1237, c_1237, c_2])).
% 4.13/1.74  tff(c_1306, plain, (![B_260]: (k1_relat_1(k7_relat_1(B_260, '#skF_1'))='#skF_1' | ~v1_relat_1(B_260))), inference(resolution, [status(thm)], [c_1301, c_1273])).
% 4.13/1.74  tff(c_2170, plain, (k1_relat_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'))='#skF_1' | ~v1_relat_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_1976, c_1306])).
% 4.13/1.74  tff(c_2180, plain, (k1_relat_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1918, c_2170])).
% 4.13/1.74  tff(c_2107, plain, (![A_395, B_396, C_397]: (k1_relset_1(A_395, B_396, C_397)=k1_relat_1(C_397) | ~m1_subset_1(C_397, k1_zfmisc_1(k2_zfmisc_1(A_395, B_396))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.13/1.74  tff(c_2114, plain, (![B_398, C_399]: (k1_relset_1('#skF_1', B_398, C_399)=k1_relat_1(C_399) | ~m1_subset_1(C_399, k1_zfmisc_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_1257, c_2107])).
% 4.13/1.74  tff(c_2119, plain, (![B_398]: (k1_relset_1('#skF_1', B_398, k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'))=k1_relat_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1')))), inference(resolution, [status(thm)], [c_1911, c_2114])).
% 4.13/1.74  tff(c_2186, plain, (![B_398]: (k1_relset_1('#skF_1', B_398, k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'))='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2180, c_2119])).
% 4.13/1.74  tff(c_36, plain, (![C_28, B_27]: (v1_funct_2(C_28, k1_xboole_0, B_27) | k1_relset_1(k1_xboole_0, B_27, C_28)!=k1_xboole_0 | ~m1_subset_1(C_28, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_27))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 4.13/1.74  tff(c_62, plain, (![C_28, B_27]: (v1_funct_2(C_28, k1_xboole_0, B_27) | k1_relset_1(k1_xboole_0, B_27, C_28)!=k1_xboole_0 | ~m1_subset_1(C_28, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_36])).
% 4.13/1.74  tff(c_2237, plain, (![C_411, B_412]: (v1_funct_2(C_411, '#skF_1', B_412) | k1_relset_1('#skF_1', B_412, C_411)!='#skF_1' | ~m1_subset_1(C_411, k1_zfmisc_1('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_1237, c_1237, c_1237, c_1237, c_62])).
% 4.13/1.74  tff(c_2239, plain, (![B_412]: (v1_funct_2(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), '#skF_1', B_412) | k1_relset_1('#skF_1', B_412, k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'))!='#skF_1')), inference(resolution, [status(thm)], [c_1911, c_2237])).
% 4.13/1.74  tff(c_2244, plain, (![B_412]: (v1_funct_2(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), '#skF_1', B_412))), inference(demodulation, [status(thm), theory('equality')], [c_2186, c_2239])).
% 4.13/1.74  tff(c_1910, plain, (~v1_funct_2(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), '#skF_1', '#skF_1')), inference(splitRight, [status(thm)], [c_1576])).
% 4.13/1.74  tff(c_2280, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2244, c_1910])).
% 4.13/1.74  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.13/1.74  
% 4.13/1.74  Inference rules
% 4.13/1.74  ----------------------
% 4.13/1.74  #Ref     : 0
% 4.13/1.74  #Sup     : 493
% 4.13/1.74  #Fact    : 0
% 4.13/1.74  #Define  : 0
% 4.13/1.74  #Split   : 16
% 4.13/1.74  #Chain   : 0
% 4.13/1.74  #Close   : 0
% 4.13/1.74  
% 4.13/1.74  Ordering : KBO
% 4.13/1.74  
% 4.13/1.74  Simplification rules
% 4.13/1.74  ----------------------
% 4.13/1.74  #Subsume      : 31
% 4.13/1.74  #Demod        : 376
% 4.13/1.74  #Tautology    : 230
% 4.13/1.74  #SimpNegUnit  : 9
% 4.13/1.74  #BackRed      : 27
% 4.13/1.74  
% 4.13/1.74  #Partial instantiations: 0
% 4.13/1.74  #Strategies tried      : 1
% 4.13/1.74  
% 4.13/1.74  Timing (in seconds)
% 4.13/1.74  ----------------------
% 4.13/1.75  Preprocessing        : 0.33
% 4.13/1.75  Parsing              : 0.18
% 4.13/1.75  CNF conversion       : 0.02
% 4.13/1.75  Main loop            : 0.60
% 4.13/1.75  Inferencing          : 0.22
% 4.13/1.75  Reduction            : 0.19
% 4.13/1.75  Demodulation         : 0.13
% 4.13/1.75  BG Simplification    : 0.03
% 4.13/1.75  Subsumption          : 0.10
% 4.13/1.75  Abstraction          : 0.03
% 4.13/1.75  MUC search           : 0.00
% 4.13/1.75  Cooper               : 0.00
% 4.13/1.75  Total                : 1.00
% 4.13/1.75  Index Insertion      : 0.00
% 4.13/1.75  Index Deletion       : 0.00
% 4.13/1.75  Index Matching       : 0.00
% 4.13/1.75  BG Taut test         : 0.00
%------------------------------------------------------------------------------
