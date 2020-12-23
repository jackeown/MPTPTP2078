%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:32 EST 2020

% Result     : Theorem 9.53s
% Output     : CNFRefutation 9.91s
% Verified   : 
% Statistics : Number of formulae       :  177 (1380 expanded)
%              Number of leaves         :   36 ( 444 expanded)
%              Depth                    :   13
%              Number of atoms          :  315 (4589 expanded)
%              Number of equality atoms :   89 (1579 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   2 average)

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

tff(f_46,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_38,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_66,axiom,(
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

tff(f_52,axiom,(
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

tff(f_56,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_44,axiom,(
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

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_31,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

tff(c_54,plain,(
    r1_tarski('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_12,plain,(
    ! [A_8,B_9] : v1_relat_1(k2_zfmisc_1(A_8,B_9)) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_56,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_156,plain,(
    ! [B_72,A_73] :
      ( v1_relat_1(B_72)
      | ~ m1_subset_1(B_72,k1_zfmisc_1(A_73))
      | ~ v1_relat_1(A_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_159,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_56,c_156])).

tff(c_162,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_159])).

tff(c_52,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_62,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_58,plain,(
    v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_10418,plain,(
    ! [A_1130,B_1131,C_1132] :
      ( k1_relset_1(A_1130,B_1131,C_1132) = k1_relat_1(C_1132)
      | ~ m1_subset_1(C_1132,k1_zfmisc_1(k2_zfmisc_1(A_1130,B_1131))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_10426,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_56,c_10418])).

tff(c_10728,plain,(
    ! [B_1183,A_1184,C_1185] :
      ( k1_xboole_0 = B_1183
      | k1_relset_1(A_1184,B_1183,C_1185) = A_1184
      | ~ v1_funct_2(C_1185,A_1184,B_1183)
      | ~ m1_subset_1(C_1185,k1_zfmisc_1(k2_zfmisc_1(A_1184,B_1183))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_10740,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_56,c_10728])).

tff(c_10748,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_10426,c_10740])).

tff(c_10749,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_10748])).

tff(c_14,plain,(
    ! [B_11,A_10] :
      ( k1_relat_1(k7_relat_1(B_11,A_10)) = A_10
      | ~ r1_tarski(A_10,k1_relat_1(B_11))
      | ~ v1_relat_1(B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_10770,plain,(
    ! [A_10] :
      ( k1_relat_1(k7_relat_1('#skF_4',A_10)) = A_10
      | ~ r1_tarski(A_10,'#skF_1')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10749,c_14])).

tff(c_10798,plain,(
    ! [A_1187] :
      ( k1_relat_1(k7_relat_1('#skF_4',A_1187)) = A_1187
      | ~ r1_tarski(A_1187,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_162,c_10770])).

tff(c_60,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_10510,plain,(
    ! [A_1153,B_1154,C_1155,D_1156] :
      ( k2_partfun1(A_1153,B_1154,C_1155,D_1156) = k7_relat_1(C_1155,D_1156)
      | ~ m1_subset_1(C_1155,k1_zfmisc_1(k2_zfmisc_1(A_1153,B_1154)))
      | ~ v1_funct_1(C_1155) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_10516,plain,(
    ! [D_1156] :
      ( k2_partfun1('#skF_1','#skF_2','#skF_4',D_1156) = k7_relat_1('#skF_4',D_1156)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_56,c_10510])).

tff(c_10523,plain,(
    ! [D_1156] : k2_partfun1('#skF_1','#skF_2','#skF_4',D_1156) = k7_relat_1('#skF_4',D_1156) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_10516])).

tff(c_394,plain,(
    ! [A_132,B_133,C_134,D_135] :
      ( k2_partfun1(A_132,B_133,C_134,D_135) = k7_relat_1(C_134,D_135)
      | ~ m1_subset_1(C_134,k1_zfmisc_1(k2_zfmisc_1(A_132,B_133)))
      | ~ v1_funct_1(C_134) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_400,plain,(
    ! [D_135] :
      ( k2_partfun1('#skF_1','#skF_2','#skF_4',D_135) = k7_relat_1('#skF_4',D_135)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_56,c_394])).

tff(c_405,plain,(
    ! [D_135] : k2_partfun1('#skF_1','#skF_2','#skF_4',D_135) = k7_relat_1('#skF_4',D_135) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_400])).

tff(c_965,plain,(
    ! [A_183,B_184,C_185,D_186] :
      ( m1_subset_1(k2_partfun1(A_183,B_184,C_185,D_186),k1_zfmisc_1(k2_zfmisc_1(A_183,B_184)))
      | ~ m1_subset_1(C_185,k1_zfmisc_1(k2_zfmisc_1(A_183,B_184)))
      | ~ v1_funct_1(C_185) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_1005,plain,(
    ! [D_135] :
      ( m1_subset_1(k7_relat_1('#skF_4',D_135),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_405,c_965])).

tff(c_1022,plain,(
    ! [D_187] : m1_subset_1(k7_relat_1('#skF_4',D_187),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_56,c_1005])).

tff(c_16,plain,(
    ! [C_14,A_12,B_13] :
      ( v1_relat_1(C_14)
      | ~ m1_subset_1(C_14,k1_zfmisc_1(k2_zfmisc_1(A_12,B_13))) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_1063,plain,(
    ! [D_187] : v1_relat_1(k7_relat_1('#skF_4',D_187)) ),
    inference(resolution,[status(thm)],[c_1022,c_16])).

tff(c_18,plain,(
    ! [C_17,B_16,A_15] :
      ( v5_relat_1(C_17,B_16)
      | ~ m1_subset_1(C_17,k1_zfmisc_1(k2_zfmisc_1(A_15,B_16))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_1061,plain,(
    ! [D_187] : v5_relat_1(k7_relat_1('#skF_4',D_187),'#skF_2') ),
    inference(resolution,[status(thm)],[c_1022,c_18])).

tff(c_10,plain,(
    ! [B_7,A_6] :
      ( r1_tarski(k2_relat_1(B_7),A_6)
      | ~ v5_relat_1(B_7,A_6)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_230,plain,(
    ! [A_99,B_100,C_101,D_102] :
      ( v1_funct_1(k2_partfun1(A_99,B_100,C_101,D_102))
      | ~ m1_subset_1(C_101,k1_zfmisc_1(k2_zfmisc_1(A_99,B_100)))
      | ~ v1_funct_1(C_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_232,plain,(
    ! [D_102] :
      ( v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4',D_102))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_56,c_230])).

tff(c_235,plain,(
    ! [D_102] : v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4',D_102)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_232])).

tff(c_406,plain,(
    ! [D_102] : v1_funct_1(k7_relat_1('#skF_4',D_102)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_405,c_235])).

tff(c_215,plain,(
    ! [A_91,B_92,C_93] :
      ( k1_relset_1(A_91,B_92,C_93) = k1_relat_1(C_93)
      | ~ m1_subset_1(C_93,k1_zfmisc_1(k2_zfmisc_1(A_91,B_92))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_219,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_56,c_215])).

tff(c_827,plain,(
    ! [B_177,A_178,C_179] :
      ( k1_xboole_0 = B_177
      | k1_relset_1(A_178,B_177,C_179) = A_178
      | ~ v1_funct_2(C_179,A_178,B_177)
      | ~ m1_subset_1(C_179,k1_zfmisc_1(k2_zfmisc_1(A_178,B_177))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_836,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_56,c_827])).

tff(c_841,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_219,c_836])).

tff(c_842,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_841])).

tff(c_865,plain,(
    ! [A_10] :
      ( k1_relat_1(k7_relat_1('#skF_4',A_10)) = A_10
      | ~ r1_tarski(A_10,'#skF_1')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_842,c_14])).

tff(c_896,plain,(
    ! [A_182] :
      ( k1_relat_1(k7_relat_1('#skF_4',A_182)) = A_182
      | ~ r1_tarski(A_182,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_162,c_865])).

tff(c_44,plain,(
    ! [B_36,A_35] :
      ( m1_subset_1(B_36,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_36),A_35)))
      | ~ r1_tarski(k2_relat_1(B_36),A_35)
      | ~ v1_funct_1(B_36)
      | ~ v1_relat_1(B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_919,plain,(
    ! [A_182,A_35] :
      ( m1_subset_1(k7_relat_1('#skF_4',A_182),k1_zfmisc_1(k2_zfmisc_1(A_182,A_35)))
      | ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_4',A_182)),A_35)
      | ~ v1_funct_1(k7_relat_1('#skF_4',A_182))
      | ~ v1_relat_1(k7_relat_1('#skF_4',A_182))
      | ~ r1_tarski(A_182,'#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_896,c_44])).

tff(c_952,plain,(
    ! [A_182,A_35] :
      ( m1_subset_1(k7_relat_1('#skF_4',A_182),k1_zfmisc_1(k2_zfmisc_1(A_182,A_35)))
      | ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_4',A_182)),A_35)
      | ~ v1_relat_1(k7_relat_1('#skF_4',A_182))
      | ~ r1_tarski(A_182,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_406,c_919])).

tff(c_10247,plain,(
    ! [A_1121,A_1122] :
      ( m1_subset_1(k7_relat_1('#skF_4',A_1121),k1_zfmisc_1(k2_zfmisc_1(A_1121,A_1122)))
      | ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_4',A_1121)),A_1122)
      | ~ r1_tarski(A_1121,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1063,c_952])).

tff(c_145,plain,(
    ! [A_68,B_69,C_70,D_71] :
      ( v1_funct_1(k2_partfun1(A_68,B_69,C_70,D_71))
      | ~ m1_subset_1(C_70,k1_zfmisc_1(k2_zfmisc_1(A_68,B_69)))
      | ~ v1_funct_1(C_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_147,plain,(
    ! [D_71] :
      ( v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4',D_71))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_56,c_145])).

tff(c_150,plain,(
    ! [D_71] : v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4',D_71)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_147])).

tff(c_50,plain,
    ( ~ m1_subset_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_2(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_3','#skF_2')
    | ~ v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_71,plain,(
    ~ v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_153,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_150,c_71])).

tff(c_154,plain,
    ( ~ v1_funct_2(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_3','#skF_2')
    | ~ m1_subset_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_185,plain,(
    ~ m1_subset_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_154])).

tff(c_407,plain,(
    ~ m1_subset_1(k7_relat_1('#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_405,c_185])).

tff(c_10275,plain,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_4','#skF_3')),'#skF_2')
    | ~ r1_tarski('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_10247,c_407])).

tff(c_10338,plain,(
    ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_4','#skF_3')),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_10275])).

tff(c_10362,plain,
    ( ~ v5_relat_1(k7_relat_1('#skF_4','#skF_3'),'#skF_2')
    | ~ v1_relat_1(k7_relat_1('#skF_4','#skF_3')) ),
    inference(resolution,[status(thm)],[c_10,c_10338])).

tff(c_10366,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1063,c_1061,c_10362])).

tff(c_10367,plain,(
    ~ v1_funct_2(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_154])).

tff(c_10532,plain,(
    ~ v1_funct_2(k7_relat_1('#skF_4','#skF_3'),'#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10523,c_10367])).

tff(c_10368,plain,(
    m1_subset_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_154])).

tff(c_10425,plain,(
    k1_relset_1('#skF_3','#skF_2',k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')) = k1_relat_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')) ),
    inference(resolution,[status(thm)],[c_10368,c_10418])).

tff(c_10526,plain,(
    k1_relset_1('#skF_3','#skF_2',k7_relat_1('#skF_4','#skF_3')) = k1_relat_1(k7_relat_1('#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10523,c_10523,c_10425])).

tff(c_10531,plain,(
    m1_subset_1(k7_relat_1('#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10523,c_10368])).

tff(c_10650,plain,(
    ! [B_1164,C_1165,A_1166] :
      ( k1_xboole_0 = B_1164
      | v1_funct_2(C_1165,A_1166,B_1164)
      | k1_relset_1(A_1166,B_1164,C_1165) != A_1166
      | ~ m1_subset_1(C_1165,k1_zfmisc_1(k2_zfmisc_1(A_1166,B_1164))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_10653,plain,
    ( k1_xboole_0 = '#skF_2'
    | v1_funct_2(k7_relat_1('#skF_4','#skF_3'),'#skF_3','#skF_2')
    | k1_relset_1('#skF_3','#skF_2',k7_relat_1('#skF_4','#skF_3')) != '#skF_3' ),
    inference(resolution,[status(thm)],[c_10531,c_10650])).

tff(c_10664,plain,
    ( k1_xboole_0 = '#skF_2'
    | v1_funct_2(k7_relat_1('#skF_4','#skF_3'),'#skF_3','#skF_2')
    | k1_relat_1(k7_relat_1('#skF_4','#skF_3')) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10526,c_10653])).

tff(c_10665,plain,(
    k1_relat_1(k7_relat_1('#skF_4','#skF_3')) != '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_10532,c_62,c_10664])).

tff(c_10816,plain,(
    ~ r1_tarski('#skF_3','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_10798,c_10665])).

tff(c_10855,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_10816])).

tff(c_10856,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_10858,plain,(
    ! [A_1] : r1_tarski('#skF_1',A_1) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10856,c_2])).

tff(c_10857,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_10863,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10856,c_10857])).

tff(c_10889,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10863,c_56])).

tff(c_10890,plain,(
    ! [B_1192,A_1193] :
      ( v1_relat_1(B_1192)
      | ~ m1_subset_1(B_1192,k1_zfmisc_1(A_1193))
      | ~ v1_relat_1(A_1193) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_10893,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_1')) ),
    inference(resolution,[status(thm)],[c_10889,c_10890])).

tff(c_10896,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_10893])).

tff(c_10864,plain,(
    v1_funct_2('#skF_4','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10863,c_58])).

tff(c_12206,plain,(
    ! [A_1384,B_1385,C_1386] :
      ( k1_relset_1(A_1384,B_1385,C_1386) = k1_relat_1(C_1386)
      | ~ m1_subset_1(C_1386,k1_zfmisc_1(k2_zfmisc_1(A_1384,B_1385))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_12214,plain,(
    k1_relset_1('#skF_1','#skF_1','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_10889,c_12206])).

tff(c_34,plain,(
    ! [B_25,C_26] :
      ( k1_relset_1(k1_xboole_0,B_25,C_26) = k1_xboole_0
      | ~ v1_funct_2(C_26,k1_xboole_0,B_25)
      | ~ m1_subset_1(C_26,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_25))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_12317,plain,(
    ! [B_1403,C_1404] :
      ( k1_relset_1('#skF_1',B_1403,C_1404) = '#skF_1'
      | ~ v1_funct_2(C_1404,'#skF_1',B_1403)
      | ~ m1_subset_1(C_1404,k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_1403))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10856,c_10856,c_10856,c_10856,c_34])).

tff(c_12323,plain,
    ( k1_relset_1('#skF_1','#skF_1','#skF_4') = '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_10889,c_12317])).

tff(c_12328,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10864,c_12214,c_12323])).

tff(c_12341,plain,(
    ! [A_10] :
      ( k1_relat_1(k7_relat_1('#skF_4',A_10)) = A_10
      | ~ r1_tarski(A_10,'#skF_1')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12328,c_14])).

tff(c_12349,plain,(
    ! [A_10] :
      ( k1_relat_1(k7_relat_1('#skF_4',A_10)) = A_10
      | ~ r1_tarski(A_10,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10896,c_12341])).

tff(c_11021,plain,(
    ! [C_1229,B_1230,A_1231] :
      ( v5_relat_1(C_1229,B_1230)
      | ~ m1_subset_1(C_1229,k1_zfmisc_1(k2_zfmisc_1(A_1231,B_1230))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_11025,plain,(
    v5_relat_1('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_10889,c_11021])).

tff(c_11026,plain,(
    ! [B_1232,A_1233] :
      ( r1_tarski(k2_relat_1(B_1232),A_1233)
      | ~ v5_relat_1(B_1232,A_1233)
      | ~ v1_relat_1(B_1232) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_4,plain,(
    ! [A_2] :
      ( k1_xboole_0 = A_2
      | ~ r1_tarski(A_2,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_10871,plain,(
    ! [A_2] :
      ( A_2 = '#skF_1'
      | ~ r1_tarski(A_2,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10856,c_10856,c_4])).

tff(c_11036,plain,(
    ! [B_1234] :
      ( k2_relat_1(B_1234) = '#skF_1'
      | ~ v5_relat_1(B_1234,'#skF_1')
      | ~ v1_relat_1(B_1234) ) ),
    inference(resolution,[status(thm)],[c_11026,c_10871])).

tff(c_11039,plain,
    ( k2_relat_1('#skF_4') = '#skF_1'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_11025,c_11036])).

tff(c_11042,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10896,c_11039])).

tff(c_12335,plain,(
    ! [A_35] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1',A_35)))
      | ~ r1_tarski(k2_relat_1('#skF_4'),A_35)
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12328,c_44])).

tff(c_12345,plain,(
    ! [A_35] : m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1',A_35))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10896,c_60,c_10858,c_11042,c_12335])).

tff(c_12660,plain,(
    ! [A_1430,B_1431,C_1432,D_1433] :
      ( k2_partfun1(A_1430,B_1431,C_1432,D_1433) = k7_relat_1(C_1432,D_1433)
      | ~ m1_subset_1(C_1432,k1_zfmisc_1(k2_zfmisc_1(A_1430,B_1431)))
      | ~ v1_funct_1(C_1432) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_12664,plain,(
    ! [A_35,D_1433] :
      ( k2_partfun1('#skF_1',A_35,'#skF_4',D_1433) = k7_relat_1('#skF_4',D_1433)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_12345,c_12660])).

tff(c_12672,plain,(
    ! [A_35,D_1433] : k2_partfun1('#skF_1',A_35,'#skF_4',D_1433) = k7_relat_1('#skF_4',D_1433) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_12664])).

tff(c_11097,plain,(
    ! [A_1243,B_1244,C_1245] :
      ( k1_relset_1(A_1243,B_1244,C_1245) = k1_relat_1(C_1245)
      | ~ m1_subset_1(C_1245,k1_zfmisc_1(k2_zfmisc_1(A_1243,B_1244))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_11101,plain,(
    k1_relset_1('#skF_1','#skF_1','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_10889,c_11097])).

tff(c_11128,plain,(
    ! [B_1255,C_1256] :
      ( k1_relset_1('#skF_1',B_1255,C_1256) = '#skF_1'
      | ~ v1_funct_2(C_1256,'#skF_1',B_1255)
      | ~ m1_subset_1(C_1256,k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_1255))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10856,c_10856,c_10856,c_10856,c_34])).

tff(c_11131,plain,
    ( k1_relset_1('#skF_1','#skF_1','#skF_4') = '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_10889,c_11128])).

tff(c_11134,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10864,c_11101,c_11131])).

tff(c_11178,plain,(
    ! [A_35] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1',A_35)))
      | ~ r1_tarski(k2_relat_1('#skF_4'),A_35)
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_11134,c_44])).

tff(c_11188,plain,(
    ! [A_35] : m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1',A_35))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10896,c_60,c_10858,c_11042,c_11178])).

tff(c_11443,plain,(
    ! [A_1282,B_1283,C_1284,D_1285] :
      ( k2_partfun1(A_1282,B_1283,C_1284,D_1285) = k7_relat_1(C_1284,D_1285)
      | ~ m1_subset_1(C_1284,k1_zfmisc_1(k2_zfmisc_1(A_1282,B_1283)))
      | ~ v1_funct_1(C_1284) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_11445,plain,(
    ! [A_35,D_1285] :
      ( k2_partfun1('#skF_1',A_35,'#skF_4',D_1285) = k7_relat_1('#skF_4',D_1285)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_11188,c_11443])).

tff(c_11450,plain,(
    ! [A_35,D_1285] : k2_partfun1('#skF_1',A_35,'#skF_4',D_1285) = k7_relat_1('#skF_4',D_1285) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_11445])).

tff(c_12019,plain,(
    ! [A_1366,B_1367,C_1368,D_1369] :
      ( m1_subset_1(k2_partfun1(A_1366,B_1367,C_1368,D_1369),k1_zfmisc_1(k2_zfmisc_1(A_1366,B_1367)))
      | ~ m1_subset_1(C_1368,k1_zfmisc_1(k2_zfmisc_1(A_1366,B_1367)))
      | ~ v1_funct_1(C_1368) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_12062,plain,(
    ! [D_1285,A_35] :
      ( m1_subset_1(k7_relat_1('#skF_4',D_1285),k1_zfmisc_1(k2_zfmisc_1('#skF_1',A_35)))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1',A_35)))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_11450,c_12019])).

tff(c_12078,plain,(
    ! [D_1285,A_35] : m1_subset_1(k7_relat_1('#skF_4',D_1285),k1_zfmisc_1(k2_zfmisc_1('#skF_1',A_35))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_11188,c_12062])).

tff(c_11003,plain,(
    ! [A_1220,B_1221,C_1222,D_1223] :
      ( v1_funct_1(k2_partfun1(A_1220,B_1221,C_1222,D_1223))
      | ~ m1_subset_1(C_1222,k1_zfmisc_1(k2_zfmisc_1(A_1220,B_1221)))
      | ~ v1_funct_1(C_1222) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_11005,plain,(
    ! [D_1223] :
      ( v1_funct_1(k2_partfun1('#skF_1','#skF_1','#skF_4',D_1223))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_10889,c_11003])).

tff(c_11008,plain,(
    ! [D_1223] : v1_funct_1(k2_partfun1('#skF_1','#skF_1','#skF_4',D_1223)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_11005])).

tff(c_10872,plain,(
    ! [A_1191] :
      ( A_1191 = '#skF_1'
      | ~ r1_tarski(A_1191,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10856,c_10856,c_4])).

tff(c_10882,plain,(
    '#skF_3' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_54,c_10872])).

tff(c_10897,plain,
    ( ~ m1_subset_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v1_funct_2(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),'#skF_1','#skF_1')
    | ~ v1_funct_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10882,c_10863,c_10882,c_10882,c_10863,c_10863,c_10882,c_10882,c_10863,c_10863,c_50])).

tff(c_10898,plain,(
    ~ v1_funct_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_10897])).

tff(c_11011,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_11008,c_10898])).

tff(c_11012,plain,
    ( ~ v1_funct_2(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),'#skF_1','#skF_1')
    | ~ m1_subset_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_10897])).

tff(c_11043,plain,(
    ~ m1_subset_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_11012])).

tff(c_11453,plain,(
    ~ m1_subset_1(k7_relat_1('#skF_4','#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11450,c_11043])).

tff(c_12102,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12078,c_11453])).

tff(c_12103,plain,(
    ~ v1_funct_2(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),'#skF_1','#skF_1') ),
    inference(splitRight,[status(thm)],[c_11012])).

tff(c_12104,plain,(
    m1_subset_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_11012])).

tff(c_12213,plain,(
    k1_relset_1('#skF_1','#skF_1',k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1')) = k1_relat_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1')) ),
    inference(resolution,[status(thm)],[c_12104,c_12206])).

tff(c_30,plain,(
    ! [C_26,B_25] :
      ( v1_funct_2(C_26,k1_xboole_0,B_25)
      | k1_relset_1(k1_xboole_0,B_25,C_26) != k1_xboole_0
      | ~ m1_subset_1(C_26,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_25))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_12448,plain,(
    ! [C_1411,B_1412] :
      ( v1_funct_2(C_1411,'#skF_1',B_1412)
      | k1_relset_1('#skF_1',B_1412,C_1411) != '#skF_1'
      | ~ m1_subset_1(C_1411,k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_1412))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10856,c_10856,c_10856,c_10856,c_30])).

tff(c_12454,plain,
    ( v1_funct_2(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),'#skF_1','#skF_1')
    | k1_relset_1('#skF_1','#skF_1',k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1')) != '#skF_1' ),
    inference(resolution,[status(thm)],[c_12104,c_12448])).

tff(c_12459,plain,
    ( v1_funct_2(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),'#skF_1','#skF_1')
    | k1_relat_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1')) != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12213,c_12454])).

tff(c_12460,plain,(
    k1_relat_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1')) != '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_12103,c_12459])).

tff(c_12679,plain,(
    k1_relat_1(k7_relat_1('#skF_4','#skF_1')) != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12672,c_12460])).

tff(c_12733,plain,(
    ~ r1_tarski('#skF_1','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_12349,c_12679])).

tff(c_12740,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10858,c_12733])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:24:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.53/3.63  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.53/3.65  
% 9.53/3.65  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.53/3.65  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_partfun1 > k1_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 9.53/3.65  
% 9.53/3.65  %Foreground sorts:
% 9.53/3.65  
% 9.53/3.65  
% 9.53/3.65  %Background operators:
% 9.53/3.65  
% 9.53/3.65  
% 9.53/3.65  %Foreground operators:
% 9.53/3.65  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 9.53/3.65  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.53/3.65  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 9.53/3.65  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 9.53/3.65  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 9.53/3.65  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 9.53/3.65  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 9.53/3.65  tff('#skF_2', type, '#skF_2': $i).
% 9.53/3.65  tff('#skF_3', type, '#skF_3': $i).
% 9.53/3.65  tff('#skF_1', type, '#skF_1': $i).
% 9.53/3.65  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 9.53/3.65  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 9.53/3.65  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 9.53/3.65  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.53/3.65  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 9.53/3.65  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 9.53/3.66  tff('#skF_4', type, '#skF_4': $i).
% 9.53/3.66  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.53/3.66  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 9.53/3.66  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 9.53/3.66  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 9.53/3.66  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 9.53/3.66  
% 9.91/3.68  tff(f_138, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_tarski(C, A) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | ((v1_funct_1(k2_partfun1(A, B, D, C)) & v1_funct_2(k2_partfun1(A, B, D, C), C, B)) & m1_subset_1(k2_partfun1(A, B, D, C), k1_zfmisc_1(k2_zfmisc_1(C, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_funct_2)).
% 9.91/3.68  tff(f_46, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 9.91/3.68  tff(f_38, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 9.91/3.68  tff(f_66, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 9.91/3.68  tff(f_92, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 9.91/3.68  tff(f_52, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => (k1_relat_1(k7_relat_1(B, A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_relat_1)).
% 9.91/3.68  tff(f_106, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 9.91/3.68  tff(f_100, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (v1_funct_1(k2_partfun1(A, B, C, D)) & m1_subset_1(k2_partfun1(A, B, C, D), k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_partfun1)).
% 9.91/3.68  tff(f_56, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 9.91/3.68  tff(f_62, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 9.91/3.68  tff(f_44, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 9.91/3.68  tff(f_118, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(k2_relat_1(B), A) => ((v1_funct_1(B) & v1_funct_2(B, k1_relat_1(B), A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B), A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_funct_2)).
% 9.91/3.68  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 9.91/3.68  tff(f_31, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_1)).
% 9.91/3.68  tff(c_54, plain, (r1_tarski('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_138])).
% 9.91/3.68  tff(c_12, plain, (![A_8, B_9]: (v1_relat_1(k2_zfmisc_1(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 9.91/3.68  tff(c_56, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_138])).
% 9.91/3.68  tff(c_156, plain, (![B_72, A_73]: (v1_relat_1(B_72) | ~m1_subset_1(B_72, k1_zfmisc_1(A_73)) | ~v1_relat_1(A_73))), inference(cnfTransformation, [status(thm)], [f_38])).
% 9.91/3.68  tff(c_159, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_56, c_156])).
% 9.91/3.68  tff(c_162, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_12, c_159])).
% 9.91/3.68  tff(c_52, plain, (k1_xboole_0='#skF_1' | k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_138])).
% 9.91/3.68  tff(c_62, plain, (k1_xboole_0!='#skF_2'), inference(splitLeft, [status(thm)], [c_52])).
% 9.91/3.68  tff(c_58, plain, (v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_138])).
% 9.91/3.68  tff(c_10418, plain, (![A_1130, B_1131, C_1132]: (k1_relset_1(A_1130, B_1131, C_1132)=k1_relat_1(C_1132) | ~m1_subset_1(C_1132, k1_zfmisc_1(k2_zfmisc_1(A_1130, B_1131))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 9.91/3.68  tff(c_10426, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_56, c_10418])).
% 9.91/3.68  tff(c_10728, plain, (![B_1183, A_1184, C_1185]: (k1_xboole_0=B_1183 | k1_relset_1(A_1184, B_1183, C_1185)=A_1184 | ~v1_funct_2(C_1185, A_1184, B_1183) | ~m1_subset_1(C_1185, k1_zfmisc_1(k2_zfmisc_1(A_1184, B_1183))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 9.91/3.68  tff(c_10740, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_1' | ~v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_56, c_10728])).
% 9.91/3.68  tff(c_10748, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_58, c_10426, c_10740])).
% 9.91/3.68  tff(c_10749, plain, (k1_relat_1('#skF_4')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_62, c_10748])).
% 9.91/3.68  tff(c_14, plain, (![B_11, A_10]: (k1_relat_1(k7_relat_1(B_11, A_10))=A_10 | ~r1_tarski(A_10, k1_relat_1(B_11)) | ~v1_relat_1(B_11))), inference(cnfTransformation, [status(thm)], [f_52])).
% 9.91/3.68  tff(c_10770, plain, (![A_10]: (k1_relat_1(k7_relat_1('#skF_4', A_10))=A_10 | ~r1_tarski(A_10, '#skF_1') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_10749, c_14])).
% 9.91/3.68  tff(c_10798, plain, (![A_1187]: (k1_relat_1(k7_relat_1('#skF_4', A_1187))=A_1187 | ~r1_tarski(A_1187, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_162, c_10770])).
% 9.91/3.68  tff(c_60, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_138])).
% 9.91/3.68  tff(c_10510, plain, (![A_1153, B_1154, C_1155, D_1156]: (k2_partfun1(A_1153, B_1154, C_1155, D_1156)=k7_relat_1(C_1155, D_1156) | ~m1_subset_1(C_1155, k1_zfmisc_1(k2_zfmisc_1(A_1153, B_1154))) | ~v1_funct_1(C_1155))), inference(cnfTransformation, [status(thm)], [f_106])).
% 9.91/3.68  tff(c_10516, plain, (![D_1156]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_1156)=k7_relat_1('#skF_4', D_1156) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_56, c_10510])).
% 9.91/3.68  tff(c_10523, plain, (![D_1156]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_1156)=k7_relat_1('#skF_4', D_1156))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_10516])).
% 9.91/3.68  tff(c_394, plain, (![A_132, B_133, C_134, D_135]: (k2_partfun1(A_132, B_133, C_134, D_135)=k7_relat_1(C_134, D_135) | ~m1_subset_1(C_134, k1_zfmisc_1(k2_zfmisc_1(A_132, B_133))) | ~v1_funct_1(C_134))), inference(cnfTransformation, [status(thm)], [f_106])).
% 9.91/3.68  tff(c_400, plain, (![D_135]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_135)=k7_relat_1('#skF_4', D_135) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_56, c_394])).
% 9.91/3.68  tff(c_405, plain, (![D_135]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_135)=k7_relat_1('#skF_4', D_135))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_400])).
% 9.91/3.68  tff(c_965, plain, (![A_183, B_184, C_185, D_186]: (m1_subset_1(k2_partfun1(A_183, B_184, C_185, D_186), k1_zfmisc_1(k2_zfmisc_1(A_183, B_184))) | ~m1_subset_1(C_185, k1_zfmisc_1(k2_zfmisc_1(A_183, B_184))) | ~v1_funct_1(C_185))), inference(cnfTransformation, [status(thm)], [f_100])).
% 9.91/3.68  tff(c_1005, plain, (![D_135]: (m1_subset_1(k7_relat_1('#skF_4', D_135), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_405, c_965])).
% 9.91/3.68  tff(c_1022, plain, (![D_187]: (m1_subset_1(k7_relat_1('#skF_4', D_187), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_56, c_1005])).
% 9.91/3.68  tff(c_16, plain, (![C_14, A_12, B_13]: (v1_relat_1(C_14) | ~m1_subset_1(C_14, k1_zfmisc_1(k2_zfmisc_1(A_12, B_13))))), inference(cnfTransformation, [status(thm)], [f_56])).
% 9.91/3.68  tff(c_1063, plain, (![D_187]: (v1_relat_1(k7_relat_1('#skF_4', D_187)))), inference(resolution, [status(thm)], [c_1022, c_16])).
% 9.91/3.68  tff(c_18, plain, (![C_17, B_16, A_15]: (v5_relat_1(C_17, B_16) | ~m1_subset_1(C_17, k1_zfmisc_1(k2_zfmisc_1(A_15, B_16))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 9.91/3.68  tff(c_1061, plain, (![D_187]: (v5_relat_1(k7_relat_1('#skF_4', D_187), '#skF_2'))), inference(resolution, [status(thm)], [c_1022, c_18])).
% 9.91/3.68  tff(c_10, plain, (![B_7, A_6]: (r1_tarski(k2_relat_1(B_7), A_6) | ~v5_relat_1(B_7, A_6) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_44])).
% 9.91/3.68  tff(c_230, plain, (![A_99, B_100, C_101, D_102]: (v1_funct_1(k2_partfun1(A_99, B_100, C_101, D_102)) | ~m1_subset_1(C_101, k1_zfmisc_1(k2_zfmisc_1(A_99, B_100))) | ~v1_funct_1(C_101))), inference(cnfTransformation, [status(thm)], [f_100])).
% 9.91/3.68  tff(c_232, plain, (![D_102]: (v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_102)) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_56, c_230])).
% 9.91/3.68  tff(c_235, plain, (![D_102]: (v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_102)))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_232])).
% 9.91/3.68  tff(c_406, plain, (![D_102]: (v1_funct_1(k7_relat_1('#skF_4', D_102)))), inference(demodulation, [status(thm), theory('equality')], [c_405, c_235])).
% 9.91/3.68  tff(c_215, plain, (![A_91, B_92, C_93]: (k1_relset_1(A_91, B_92, C_93)=k1_relat_1(C_93) | ~m1_subset_1(C_93, k1_zfmisc_1(k2_zfmisc_1(A_91, B_92))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 9.91/3.68  tff(c_219, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_56, c_215])).
% 9.91/3.68  tff(c_827, plain, (![B_177, A_178, C_179]: (k1_xboole_0=B_177 | k1_relset_1(A_178, B_177, C_179)=A_178 | ~v1_funct_2(C_179, A_178, B_177) | ~m1_subset_1(C_179, k1_zfmisc_1(k2_zfmisc_1(A_178, B_177))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 9.91/3.68  tff(c_836, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_1' | ~v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_56, c_827])).
% 9.91/3.68  tff(c_841, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_58, c_219, c_836])).
% 9.91/3.68  tff(c_842, plain, (k1_relat_1('#skF_4')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_62, c_841])).
% 9.91/3.68  tff(c_865, plain, (![A_10]: (k1_relat_1(k7_relat_1('#skF_4', A_10))=A_10 | ~r1_tarski(A_10, '#skF_1') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_842, c_14])).
% 9.91/3.68  tff(c_896, plain, (![A_182]: (k1_relat_1(k7_relat_1('#skF_4', A_182))=A_182 | ~r1_tarski(A_182, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_162, c_865])).
% 9.91/3.68  tff(c_44, plain, (![B_36, A_35]: (m1_subset_1(B_36, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_36), A_35))) | ~r1_tarski(k2_relat_1(B_36), A_35) | ~v1_funct_1(B_36) | ~v1_relat_1(B_36))), inference(cnfTransformation, [status(thm)], [f_118])).
% 9.91/3.68  tff(c_919, plain, (![A_182, A_35]: (m1_subset_1(k7_relat_1('#skF_4', A_182), k1_zfmisc_1(k2_zfmisc_1(A_182, A_35))) | ~r1_tarski(k2_relat_1(k7_relat_1('#skF_4', A_182)), A_35) | ~v1_funct_1(k7_relat_1('#skF_4', A_182)) | ~v1_relat_1(k7_relat_1('#skF_4', A_182)) | ~r1_tarski(A_182, '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_896, c_44])).
% 9.91/3.68  tff(c_952, plain, (![A_182, A_35]: (m1_subset_1(k7_relat_1('#skF_4', A_182), k1_zfmisc_1(k2_zfmisc_1(A_182, A_35))) | ~r1_tarski(k2_relat_1(k7_relat_1('#skF_4', A_182)), A_35) | ~v1_relat_1(k7_relat_1('#skF_4', A_182)) | ~r1_tarski(A_182, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_406, c_919])).
% 9.91/3.68  tff(c_10247, plain, (![A_1121, A_1122]: (m1_subset_1(k7_relat_1('#skF_4', A_1121), k1_zfmisc_1(k2_zfmisc_1(A_1121, A_1122))) | ~r1_tarski(k2_relat_1(k7_relat_1('#skF_4', A_1121)), A_1122) | ~r1_tarski(A_1121, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_1063, c_952])).
% 9.91/3.68  tff(c_145, plain, (![A_68, B_69, C_70, D_71]: (v1_funct_1(k2_partfun1(A_68, B_69, C_70, D_71)) | ~m1_subset_1(C_70, k1_zfmisc_1(k2_zfmisc_1(A_68, B_69))) | ~v1_funct_1(C_70))), inference(cnfTransformation, [status(thm)], [f_100])).
% 9.91/3.68  tff(c_147, plain, (![D_71]: (v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_71)) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_56, c_145])).
% 9.91/3.68  tff(c_150, plain, (![D_71]: (v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_71)))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_147])).
% 9.91/3.68  tff(c_50, plain, (~m1_subset_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_2(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_3', '#skF_2') | ~v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_138])).
% 9.91/3.68  tff(c_71, plain, (~v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))), inference(splitLeft, [status(thm)], [c_50])).
% 9.91/3.68  tff(c_153, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_150, c_71])).
% 9.91/3.68  tff(c_154, plain, (~v1_funct_2(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_3', '#skF_2') | ~m1_subset_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitRight, [status(thm)], [c_50])).
% 9.91/3.68  tff(c_185, plain, (~m1_subset_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitLeft, [status(thm)], [c_154])).
% 9.91/3.68  tff(c_407, plain, (~m1_subset_1(k7_relat_1('#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_405, c_185])).
% 9.91/3.68  tff(c_10275, plain, (~r1_tarski(k2_relat_1(k7_relat_1('#skF_4', '#skF_3')), '#skF_2') | ~r1_tarski('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_10247, c_407])).
% 9.91/3.68  tff(c_10338, plain, (~r1_tarski(k2_relat_1(k7_relat_1('#skF_4', '#skF_3')), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_10275])).
% 9.91/3.68  tff(c_10362, plain, (~v5_relat_1(k7_relat_1('#skF_4', '#skF_3'), '#skF_2') | ~v1_relat_1(k7_relat_1('#skF_4', '#skF_3'))), inference(resolution, [status(thm)], [c_10, c_10338])).
% 9.91/3.68  tff(c_10366, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1063, c_1061, c_10362])).
% 9.91/3.68  tff(c_10367, plain, (~v1_funct_2(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_154])).
% 9.91/3.68  tff(c_10532, plain, (~v1_funct_2(k7_relat_1('#skF_4', '#skF_3'), '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_10523, c_10367])).
% 9.91/3.68  tff(c_10368, plain, (m1_subset_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitRight, [status(thm)], [c_154])).
% 9.91/3.68  tff(c_10425, plain, (k1_relset_1('#skF_3', '#skF_2', k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))=k1_relat_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))), inference(resolution, [status(thm)], [c_10368, c_10418])).
% 9.91/3.68  tff(c_10526, plain, (k1_relset_1('#skF_3', '#skF_2', k7_relat_1('#skF_4', '#skF_3'))=k1_relat_1(k7_relat_1('#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_10523, c_10523, c_10425])).
% 9.91/3.68  tff(c_10531, plain, (m1_subset_1(k7_relat_1('#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_10523, c_10368])).
% 9.91/3.68  tff(c_10650, plain, (![B_1164, C_1165, A_1166]: (k1_xboole_0=B_1164 | v1_funct_2(C_1165, A_1166, B_1164) | k1_relset_1(A_1166, B_1164, C_1165)!=A_1166 | ~m1_subset_1(C_1165, k1_zfmisc_1(k2_zfmisc_1(A_1166, B_1164))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 9.91/3.68  tff(c_10653, plain, (k1_xboole_0='#skF_2' | v1_funct_2(k7_relat_1('#skF_4', '#skF_3'), '#skF_3', '#skF_2') | k1_relset_1('#skF_3', '#skF_2', k7_relat_1('#skF_4', '#skF_3'))!='#skF_3'), inference(resolution, [status(thm)], [c_10531, c_10650])).
% 9.91/3.68  tff(c_10664, plain, (k1_xboole_0='#skF_2' | v1_funct_2(k7_relat_1('#skF_4', '#skF_3'), '#skF_3', '#skF_2') | k1_relat_1(k7_relat_1('#skF_4', '#skF_3'))!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_10526, c_10653])).
% 9.91/3.68  tff(c_10665, plain, (k1_relat_1(k7_relat_1('#skF_4', '#skF_3'))!='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_10532, c_62, c_10664])).
% 9.91/3.68  tff(c_10816, plain, (~r1_tarski('#skF_3', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_10798, c_10665])).
% 9.91/3.68  tff(c_10855, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54, c_10816])).
% 9.91/3.68  tff(c_10856, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_52])).
% 9.91/3.68  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 9.91/3.68  tff(c_10858, plain, (![A_1]: (r1_tarski('#skF_1', A_1))), inference(demodulation, [status(thm), theory('equality')], [c_10856, c_2])).
% 9.91/3.68  tff(c_10857, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_52])).
% 9.91/3.68  tff(c_10863, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_10856, c_10857])).
% 9.91/3.68  tff(c_10889, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_10863, c_56])).
% 9.91/3.68  tff(c_10890, plain, (![B_1192, A_1193]: (v1_relat_1(B_1192) | ~m1_subset_1(B_1192, k1_zfmisc_1(A_1193)) | ~v1_relat_1(A_1193))), inference(cnfTransformation, [status(thm)], [f_38])).
% 9.91/3.68  tff(c_10893, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_1'))), inference(resolution, [status(thm)], [c_10889, c_10890])).
% 9.91/3.68  tff(c_10896, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_12, c_10893])).
% 9.91/3.68  tff(c_10864, plain, (v1_funct_2('#skF_4', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_10863, c_58])).
% 9.91/3.68  tff(c_12206, plain, (![A_1384, B_1385, C_1386]: (k1_relset_1(A_1384, B_1385, C_1386)=k1_relat_1(C_1386) | ~m1_subset_1(C_1386, k1_zfmisc_1(k2_zfmisc_1(A_1384, B_1385))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 9.91/3.68  tff(c_12214, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_10889, c_12206])).
% 9.91/3.68  tff(c_34, plain, (![B_25, C_26]: (k1_relset_1(k1_xboole_0, B_25, C_26)=k1_xboole_0 | ~v1_funct_2(C_26, k1_xboole_0, B_25) | ~m1_subset_1(C_26, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_25))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 9.91/3.68  tff(c_12317, plain, (![B_1403, C_1404]: (k1_relset_1('#skF_1', B_1403, C_1404)='#skF_1' | ~v1_funct_2(C_1404, '#skF_1', B_1403) | ~m1_subset_1(C_1404, k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_1403))))), inference(demodulation, [status(thm), theory('equality')], [c_10856, c_10856, c_10856, c_10856, c_34])).
% 9.91/3.68  tff(c_12323, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_4')='#skF_1' | ~v1_funct_2('#skF_4', '#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_10889, c_12317])).
% 9.91/3.68  tff(c_12328, plain, (k1_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_10864, c_12214, c_12323])).
% 9.91/3.68  tff(c_12341, plain, (![A_10]: (k1_relat_1(k7_relat_1('#skF_4', A_10))=A_10 | ~r1_tarski(A_10, '#skF_1') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_12328, c_14])).
% 9.91/3.68  tff(c_12349, plain, (![A_10]: (k1_relat_1(k7_relat_1('#skF_4', A_10))=A_10 | ~r1_tarski(A_10, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_10896, c_12341])).
% 9.91/3.68  tff(c_11021, plain, (![C_1229, B_1230, A_1231]: (v5_relat_1(C_1229, B_1230) | ~m1_subset_1(C_1229, k1_zfmisc_1(k2_zfmisc_1(A_1231, B_1230))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 9.91/3.68  tff(c_11025, plain, (v5_relat_1('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_10889, c_11021])).
% 9.91/3.68  tff(c_11026, plain, (![B_1232, A_1233]: (r1_tarski(k2_relat_1(B_1232), A_1233) | ~v5_relat_1(B_1232, A_1233) | ~v1_relat_1(B_1232))), inference(cnfTransformation, [status(thm)], [f_44])).
% 9.91/3.68  tff(c_4, plain, (![A_2]: (k1_xboole_0=A_2 | ~r1_tarski(A_2, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.91/3.68  tff(c_10871, plain, (![A_2]: (A_2='#skF_1' | ~r1_tarski(A_2, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_10856, c_10856, c_4])).
% 9.91/3.68  tff(c_11036, plain, (![B_1234]: (k2_relat_1(B_1234)='#skF_1' | ~v5_relat_1(B_1234, '#skF_1') | ~v1_relat_1(B_1234))), inference(resolution, [status(thm)], [c_11026, c_10871])).
% 9.91/3.68  tff(c_11039, plain, (k2_relat_1('#skF_4')='#skF_1' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_11025, c_11036])).
% 9.91/3.68  tff(c_11042, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_10896, c_11039])).
% 9.91/3.68  tff(c_12335, plain, (![A_35]: (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', A_35))) | ~r1_tarski(k2_relat_1('#skF_4'), A_35) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_12328, c_44])).
% 9.91/3.68  tff(c_12345, plain, (![A_35]: (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', A_35))))), inference(demodulation, [status(thm), theory('equality')], [c_10896, c_60, c_10858, c_11042, c_12335])).
% 9.91/3.68  tff(c_12660, plain, (![A_1430, B_1431, C_1432, D_1433]: (k2_partfun1(A_1430, B_1431, C_1432, D_1433)=k7_relat_1(C_1432, D_1433) | ~m1_subset_1(C_1432, k1_zfmisc_1(k2_zfmisc_1(A_1430, B_1431))) | ~v1_funct_1(C_1432))), inference(cnfTransformation, [status(thm)], [f_106])).
% 9.91/3.68  tff(c_12664, plain, (![A_35, D_1433]: (k2_partfun1('#skF_1', A_35, '#skF_4', D_1433)=k7_relat_1('#skF_4', D_1433) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_12345, c_12660])).
% 9.91/3.68  tff(c_12672, plain, (![A_35, D_1433]: (k2_partfun1('#skF_1', A_35, '#skF_4', D_1433)=k7_relat_1('#skF_4', D_1433))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_12664])).
% 9.91/3.68  tff(c_11097, plain, (![A_1243, B_1244, C_1245]: (k1_relset_1(A_1243, B_1244, C_1245)=k1_relat_1(C_1245) | ~m1_subset_1(C_1245, k1_zfmisc_1(k2_zfmisc_1(A_1243, B_1244))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 9.91/3.68  tff(c_11101, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_10889, c_11097])).
% 9.91/3.68  tff(c_11128, plain, (![B_1255, C_1256]: (k1_relset_1('#skF_1', B_1255, C_1256)='#skF_1' | ~v1_funct_2(C_1256, '#skF_1', B_1255) | ~m1_subset_1(C_1256, k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_1255))))), inference(demodulation, [status(thm), theory('equality')], [c_10856, c_10856, c_10856, c_10856, c_34])).
% 9.91/3.68  tff(c_11131, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_4')='#skF_1' | ~v1_funct_2('#skF_4', '#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_10889, c_11128])).
% 9.91/3.68  tff(c_11134, plain, (k1_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_10864, c_11101, c_11131])).
% 9.91/3.68  tff(c_11178, plain, (![A_35]: (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', A_35))) | ~r1_tarski(k2_relat_1('#skF_4'), A_35) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_11134, c_44])).
% 9.91/3.68  tff(c_11188, plain, (![A_35]: (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', A_35))))), inference(demodulation, [status(thm), theory('equality')], [c_10896, c_60, c_10858, c_11042, c_11178])).
% 9.91/3.68  tff(c_11443, plain, (![A_1282, B_1283, C_1284, D_1285]: (k2_partfun1(A_1282, B_1283, C_1284, D_1285)=k7_relat_1(C_1284, D_1285) | ~m1_subset_1(C_1284, k1_zfmisc_1(k2_zfmisc_1(A_1282, B_1283))) | ~v1_funct_1(C_1284))), inference(cnfTransformation, [status(thm)], [f_106])).
% 9.91/3.68  tff(c_11445, plain, (![A_35, D_1285]: (k2_partfun1('#skF_1', A_35, '#skF_4', D_1285)=k7_relat_1('#skF_4', D_1285) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_11188, c_11443])).
% 9.91/3.68  tff(c_11450, plain, (![A_35, D_1285]: (k2_partfun1('#skF_1', A_35, '#skF_4', D_1285)=k7_relat_1('#skF_4', D_1285))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_11445])).
% 9.91/3.68  tff(c_12019, plain, (![A_1366, B_1367, C_1368, D_1369]: (m1_subset_1(k2_partfun1(A_1366, B_1367, C_1368, D_1369), k1_zfmisc_1(k2_zfmisc_1(A_1366, B_1367))) | ~m1_subset_1(C_1368, k1_zfmisc_1(k2_zfmisc_1(A_1366, B_1367))) | ~v1_funct_1(C_1368))), inference(cnfTransformation, [status(thm)], [f_100])).
% 9.91/3.68  tff(c_12062, plain, (![D_1285, A_35]: (m1_subset_1(k7_relat_1('#skF_4', D_1285), k1_zfmisc_1(k2_zfmisc_1('#skF_1', A_35))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', A_35))) | ~v1_funct_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_11450, c_12019])).
% 9.91/3.68  tff(c_12078, plain, (![D_1285, A_35]: (m1_subset_1(k7_relat_1('#skF_4', D_1285), k1_zfmisc_1(k2_zfmisc_1('#skF_1', A_35))))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_11188, c_12062])).
% 9.91/3.68  tff(c_11003, plain, (![A_1220, B_1221, C_1222, D_1223]: (v1_funct_1(k2_partfun1(A_1220, B_1221, C_1222, D_1223)) | ~m1_subset_1(C_1222, k1_zfmisc_1(k2_zfmisc_1(A_1220, B_1221))) | ~v1_funct_1(C_1222))), inference(cnfTransformation, [status(thm)], [f_100])).
% 9.91/3.68  tff(c_11005, plain, (![D_1223]: (v1_funct_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', D_1223)) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_10889, c_11003])).
% 9.91/3.68  tff(c_11008, plain, (![D_1223]: (v1_funct_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', D_1223)))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_11005])).
% 9.91/3.68  tff(c_10872, plain, (![A_1191]: (A_1191='#skF_1' | ~r1_tarski(A_1191, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_10856, c_10856, c_4])).
% 9.91/3.68  tff(c_10882, plain, ('#skF_3'='#skF_1'), inference(resolution, [status(thm)], [c_54, c_10872])).
% 9.91/3.68  tff(c_10897, plain, (~m1_subset_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v1_funct_2(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), '#skF_1', '#skF_1') | ~v1_funct_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_10882, c_10863, c_10882, c_10882, c_10863, c_10863, c_10882, c_10882, c_10863, c_10863, c_50])).
% 9.91/3.68  tff(c_10898, plain, (~v1_funct_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'))), inference(splitLeft, [status(thm)], [c_10897])).
% 9.91/3.68  tff(c_11011, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_11008, c_10898])).
% 9.91/3.68  tff(c_11012, plain, (~v1_funct_2(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), '#skF_1', '#skF_1') | ~m1_subset_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitRight, [status(thm)], [c_10897])).
% 9.91/3.68  tff(c_11043, plain, (~m1_subset_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_11012])).
% 9.91/3.68  tff(c_11453, plain, (~m1_subset_1(k7_relat_1('#skF_4', '#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_11450, c_11043])).
% 9.91/3.68  tff(c_12102, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12078, c_11453])).
% 9.91/3.68  tff(c_12103, plain, (~v1_funct_2(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), '#skF_1', '#skF_1')), inference(splitRight, [status(thm)], [c_11012])).
% 9.91/3.68  tff(c_12104, plain, (m1_subset_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitRight, [status(thm)], [c_11012])).
% 9.91/3.68  tff(c_12213, plain, (k1_relset_1('#skF_1', '#skF_1', k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'))=k1_relat_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'))), inference(resolution, [status(thm)], [c_12104, c_12206])).
% 9.91/3.68  tff(c_30, plain, (![C_26, B_25]: (v1_funct_2(C_26, k1_xboole_0, B_25) | k1_relset_1(k1_xboole_0, B_25, C_26)!=k1_xboole_0 | ~m1_subset_1(C_26, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_25))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 9.91/3.68  tff(c_12448, plain, (![C_1411, B_1412]: (v1_funct_2(C_1411, '#skF_1', B_1412) | k1_relset_1('#skF_1', B_1412, C_1411)!='#skF_1' | ~m1_subset_1(C_1411, k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_1412))))), inference(demodulation, [status(thm), theory('equality')], [c_10856, c_10856, c_10856, c_10856, c_30])).
% 9.91/3.68  tff(c_12454, plain, (v1_funct_2(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), '#skF_1', '#skF_1') | k1_relset_1('#skF_1', '#skF_1', k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'))!='#skF_1'), inference(resolution, [status(thm)], [c_12104, c_12448])).
% 9.91/3.68  tff(c_12459, plain, (v1_funct_2(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), '#skF_1', '#skF_1') | k1_relat_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'))!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_12213, c_12454])).
% 9.91/3.68  tff(c_12460, plain, (k1_relat_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'))!='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_12103, c_12459])).
% 9.91/3.68  tff(c_12679, plain, (k1_relat_1(k7_relat_1('#skF_4', '#skF_1'))!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_12672, c_12460])).
% 9.91/3.68  tff(c_12733, plain, (~r1_tarski('#skF_1', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_12349, c_12679])).
% 9.91/3.68  tff(c_12740, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10858, c_12733])).
% 9.91/3.68  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.91/3.68  
% 9.91/3.68  Inference rules
% 9.91/3.68  ----------------------
% 9.91/3.68  #Ref     : 0
% 9.91/3.68  #Sup     : 2550
% 9.91/3.68  #Fact    : 0
% 9.91/3.68  #Define  : 0
% 9.91/3.68  #Split   : 20
% 9.91/3.68  #Chain   : 0
% 9.91/3.68  #Close   : 0
% 9.91/3.68  
% 9.91/3.68  Ordering : KBO
% 9.91/3.68  
% 9.91/3.68  Simplification rules
% 9.91/3.68  ----------------------
% 9.91/3.68  #Subsume      : 224
% 9.91/3.68  #Demod        : 3724
% 9.91/3.68  #Tautology    : 989
% 9.91/3.68  #SimpNegUnit  : 81
% 9.91/3.68  #BackRed      : 91
% 9.91/3.68  
% 9.91/3.68  #Partial instantiations: 0
% 9.91/3.68  #Strategies tried      : 1
% 9.91/3.68  
% 9.91/3.68  Timing (in seconds)
% 9.91/3.68  ----------------------
% 9.94/3.69  Preprocessing        : 0.34
% 9.94/3.69  Parsing              : 0.18
% 9.94/3.69  CNF conversion       : 0.02
% 9.94/3.69  Main loop            : 2.48
% 9.94/3.69  Inferencing          : 0.81
% 9.94/3.69  Reduction            : 0.98
% 9.94/3.69  Demodulation         : 0.74
% 9.94/3.69  BG Simplification    : 0.08
% 9.94/3.69  Subsumption          : 0.45
% 9.94/3.69  Abstraction          : 0.10
% 9.94/3.69  MUC search           : 0.00
% 9.94/3.69  Cooper               : 0.00
% 9.94/3.69  Total                : 2.88
% 9.94/3.69  Index Insertion      : 0.00
% 9.94/3.69  Index Deletion       : 0.00
% 9.94/3.69  Index Matching       : 0.00
% 9.94/3.69  BG Taut test         : 0.00
%------------------------------------------------------------------------------
