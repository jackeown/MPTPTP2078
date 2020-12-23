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
% DateTime   : Thu Dec  3 10:13:34 EST 2020

% Result     : Theorem 4.73s
% Output     : CNFRefutation 4.84s
% Verified   : 
% Statistics : Number of formulae       :  200 (1617 expanded)
%              Number of leaves         :   41 ( 499 expanded)
%              Depth                    :   12
%              Number of atoms          :  330 (4850 expanded)
%              Number of equality atoms :   84 (1596 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_partfun1 > k1_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_152,negated_conjecture,(
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

tff(f_63,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_80,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_53,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => k1_relat_1(k7_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).

tff(f_120,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_114,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( v1_funct_1(k2_partfun1(A,B,C,D))
        & m1_subset_1(k2_partfun1(A,B,C,D),k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_partfun1)).

tff(f_69,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_88,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_76,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc3_relset_1)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_38,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_47,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_132,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(k2_relat_1(B),A)
       => ( v1_funct_1(B)
          & v1_funct_2(B,k1_relat_1(B),A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B),A))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).

tff(f_59,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).

tff(c_66,plain,(
    r1_tarski('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_68,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_118,plain,(
    ! [C_46,A_47,B_48] :
      ( v1_relat_1(C_46)
      | ~ m1_subset_1(C_46,k1_zfmisc_1(k2_zfmisc_1(A_47,B_48))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_122,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_68,c_118])).

tff(c_64,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_84,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_64])).

tff(c_70,plain,(
    v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_1434,plain,(
    ! [A_191,B_192,C_193] :
      ( k1_relset_1(A_191,B_192,C_193) = k1_relat_1(C_193)
      | ~ m1_subset_1(C_193,k1_zfmisc_1(k2_zfmisc_1(A_191,B_192))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_1442,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_68,c_1434])).

tff(c_1778,plain,(
    ! [B_235,A_236,C_237] :
      ( k1_xboole_0 = B_235
      | k1_relset_1(A_236,B_235,C_237) = A_236
      | ~ v1_funct_2(C_237,A_236,B_235)
      | ~ m1_subset_1(C_237,k1_zfmisc_1(k2_zfmisc_1(A_236,B_235))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_1790,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_68,c_1778])).

tff(c_1798,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_1442,c_1790])).

tff(c_1799,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_1798])).

tff(c_22,plain,(
    ! [B_8,A_7] :
      ( k1_relat_1(k7_relat_1(B_8,A_7)) = A_7
      | ~ r1_tarski(A_7,k1_relat_1(B_8))
      | ~ v1_relat_1(B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1819,plain,(
    ! [A_7] :
      ( k1_relat_1(k7_relat_1('#skF_4',A_7)) = A_7
      | ~ r1_tarski(A_7,'#skF_1')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1799,c_22])).

tff(c_1839,plain,(
    ! [A_7] :
      ( k1_relat_1(k7_relat_1('#skF_4',A_7)) = A_7
      | ~ r1_tarski(A_7,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_1819])).

tff(c_72,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_1621,plain,(
    ! [A_222,B_223,C_224,D_225] :
      ( k2_partfun1(A_222,B_223,C_224,D_225) = k7_relat_1(C_224,D_225)
      | ~ m1_subset_1(C_224,k1_zfmisc_1(k2_zfmisc_1(A_222,B_223)))
      | ~ v1_funct_1(C_224) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_1627,plain,(
    ! [D_225] :
      ( k2_partfun1('#skF_1','#skF_2','#skF_4',D_225) = k7_relat_1('#skF_4',D_225)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_68,c_1621])).

tff(c_1634,plain,(
    ! [D_225] : k2_partfun1('#skF_1','#skF_2','#skF_4',D_225) = k7_relat_1('#skF_4',D_225) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_1627])).

tff(c_10,plain,(
    ! [B_3] : r1_tarski(B_3,B_3) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_409,plain,(
    ! [A_105,B_106,C_107] :
      ( k1_relset_1(A_105,B_106,C_107) = k1_relat_1(C_107)
      | ~ m1_subset_1(C_107,k1_zfmisc_1(k2_zfmisc_1(A_105,B_106))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_413,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_68,c_409])).

tff(c_737,plain,(
    ! [B_154,A_155,C_156] :
      ( k1_xboole_0 = B_154
      | k1_relset_1(A_155,B_154,C_156) = A_155
      | ~ v1_funct_2(C_156,A_155,B_154)
      | ~ m1_subset_1(C_156,k1_zfmisc_1(k2_zfmisc_1(A_155,B_154))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_746,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_68,c_737])).

tff(c_751,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_413,c_746])).

tff(c_752,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_751])).

tff(c_775,plain,(
    ! [A_7] :
      ( k1_relat_1(k7_relat_1('#skF_4',A_7)) = A_7
      | ~ r1_tarski(A_7,'#skF_1')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_752,c_22])).

tff(c_797,plain,(
    ! [A_7] :
      ( k1_relat_1(k7_relat_1('#skF_4',A_7)) = A_7
      | ~ r1_tarski(A_7,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_775])).

tff(c_616,plain,(
    ! [A_137,B_138,C_139,D_140] :
      ( k2_partfun1(A_137,B_138,C_139,D_140) = k7_relat_1(C_139,D_140)
      | ~ m1_subset_1(C_139,k1_zfmisc_1(k2_zfmisc_1(A_137,B_138)))
      | ~ v1_funct_1(C_139) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_620,plain,(
    ! [D_140] :
      ( k2_partfun1('#skF_1','#skF_2','#skF_4',D_140) = k7_relat_1('#skF_4',D_140)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_68,c_616])).

tff(c_624,plain,(
    ! [D_140] : k2_partfun1('#skF_1','#skF_2','#skF_4',D_140) = k7_relat_1('#skF_4',D_140) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_620])).

tff(c_1164,plain,(
    ! [A_175,B_176,C_177,D_178] :
      ( m1_subset_1(k2_partfun1(A_175,B_176,C_177,D_178),k1_zfmisc_1(k2_zfmisc_1(A_175,B_176)))
      | ~ m1_subset_1(C_177,k1_zfmisc_1(k2_zfmisc_1(A_175,B_176)))
      | ~ v1_funct_1(C_177) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_1204,plain,(
    ! [D_140] :
      ( m1_subset_1(k7_relat_1('#skF_4',D_140),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_624,c_1164])).

tff(c_1219,plain,(
    ! [D_179] : m1_subset_1(k7_relat_1('#skF_4',D_179),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_68,c_1204])).

tff(c_28,plain,(
    ! [C_16,B_15,A_14] :
      ( v5_relat_1(C_16,B_15)
      | ~ m1_subset_1(C_16,k1_zfmisc_1(k2_zfmisc_1(A_14,B_15))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_1265,plain,(
    ! [D_179] : v5_relat_1(k7_relat_1('#skF_4',D_179),'#skF_2') ),
    inference(resolution,[status(thm)],[c_1219,c_28])).

tff(c_1028,plain,(
    ! [A_169,B_170,C_171,D_172] :
      ( m1_subset_1(k2_partfun1(A_169,B_170,C_171,D_172),k1_zfmisc_1(k2_zfmisc_1(A_169,B_170)))
      | ~ m1_subset_1(C_171,k1_zfmisc_1(k2_zfmisc_1(A_169,B_170)))
      | ~ v1_funct_1(C_171) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_1068,plain,(
    ! [D_140] :
      ( m1_subset_1(k7_relat_1('#skF_4',D_140),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_624,c_1028])).

tff(c_1083,plain,(
    ! [D_173] : m1_subset_1(k7_relat_1('#skF_4',D_173),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_68,c_1068])).

tff(c_26,plain,(
    ! [C_13,A_11,B_12] :
      ( v1_relat_1(C_13)
      | ~ m1_subset_1(C_13,k1_zfmisc_1(k2_zfmisc_1(A_11,B_12))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_1131,plain,(
    ! [D_173] : v1_relat_1(k7_relat_1('#skF_4',D_173)) ),
    inference(resolution,[status(thm)],[c_1083,c_26])).

tff(c_643,plain,(
    ! [C_143,A_144,B_145] :
      ( m1_subset_1(C_143,k1_zfmisc_1(k2_zfmisc_1(A_144,B_145)))
      | ~ r1_tarski(k2_relat_1(C_143),B_145)
      | ~ r1_tarski(k1_relat_1(C_143),A_144)
      | ~ v1_relat_1(C_143) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_315,plain,(
    ! [A_81,B_82,C_83,D_84] :
      ( v1_funct_1(k2_partfun1(A_81,B_82,C_83,D_84))
      | ~ m1_subset_1(C_83,k1_zfmisc_1(k2_zfmisc_1(A_81,B_82)))
      | ~ v1_funct_1(C_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_317,plain,(
    ! [D_84] :
      ( v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4',D_84))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_68,c_315])).

tff(c_320,plain,(
    ! [D_84] : v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4',D_84)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_317])).

tff(c_62,plain,
    ( ~ m1_subset_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_2(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_3','#skF_2')
    | ~ v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_134,plain,(
    ~ v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_62])).

tff(c_324,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_320,c_134])).

tff(c_325,plain,
    ( ~ v1_funct_2(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_3','#skF_2')
    | ~ m1_subset_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_383,plain,(
    ~ m1_subset_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_325])).

tff(c_626,plain,(
    ~ m1_subset_1(k7_relat_1('#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_624,c_383])).

tff(c_682,plain,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_4','#skF_3')),'#skF_2')
    | ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_4','#skF_3')),'#skF_3')
    | ~ v1_relat_1(k7_relat_1('#skF_4','#skF_3')) ),
    inference(resolution,[status(thm)],[c_643,c_626])).

tff(c_992,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_4','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_682])).

tff(c_1137,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1131,c_992])).

tff(c_1139,plain,(
    v1_relat_1(k7_relat_1('#skF_4','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_682])).

tff(c_16,plain,(
    ! [B_6,A_5] :
      ( r1_tarski(k2_relat_1(B_6),A_5)
      | ~ v5_relat_1(B_6,A_5)
      | ~ v1_relat_1(B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_1138,plain,
    ( ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_4','#skF_3')),'#skF_3')
    | ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_4','#skF_3')),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_682])).

tff(c_1140,plain,(
    ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_4','#skF_3')),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_1138])).

tff(c_1143,plain,
    ( ~ v5_relat_1(k7_relat_1('#skF_4','#skF_3'),'#skF_2')
    | ~ v1_relat_1(k7_relat_1('#skF_4','#skF_3')) ),
    inference(resolution,[status(thm)],[c_16,c_1140])).

tff(c_1146,plain,(
    ~ v5_relat_1(k7_relat_1('#skF_4','#skF_3'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1139,c_1143])).

tff(c_1290,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1265,c_1146])).

tff(c_1291,plain,(
    ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_4','#skF_3')),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_1138])).

tff(c_1366,plain,
    ( ~ r1_tarski('#skF_3','#skF_3')
    | ~ r1_tarski('#skF_3','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_797,c_1291])).

tff(c_1369,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_10,c_1366])).

tff(c_1370,plain,(
    ~ v1_funct_2(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_325])).

tff(c_1642,plain,(
    ~ v1_funct_2(k7_relat_1('#skF_4','#skF_3'),'#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1634,c_1370])).

tff(c_1371,plain,(
    m1_subset_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_325])).

tff(c_1441,plain,(
    k1_relset_1('#skF_3','#skF_2',k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')) = k1_relat_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')) ),
    inference(resolution,[status(thm)],[c_1371,c_1434])).

tff(c_1635,plain,(
    k1_relset_1('#skF_3','#skF_2',k7_relat_1('#skF_4','#skF_3')) = k1_relat_1(k7_relat_1('#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1634,c_1634,c_1441])).

tff(c_1641,plain,(
    m1_subset_1(k7_relat_1('#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1634,c_1371])).

tff(c_1956,plain,(
    ! [B_242,C_243,A_244] :
      ( k1_xboole_0 = B_242
      | v1_funct_2(C_243,A_244,B_242)
      | k1_relset_1(A_244,B_242,C_243) != A_244
      | ~ m1_subset_1(C_243,k1_zfmisc_1(k2_zfmisc_1(A_244,B_242))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_1959,plain,
    ( k1_xboole_0 = '#skF_2'
    | v1_funct_2(k7_relat_1('#skF_4','#skF_3'),'#skF_3','#skF_2')
    | k1_relset_1('#skF_3','#skF_2',k7_relat_1('#skF_4','#skF_3')) != '#skF_3' ),
    inference(resolution,[status(thm)],[c_1641,c_1956])).

tff(c_1970,plain,
    ( k1_xboole_0 = '#skF_2'
    | v1_funct_2(k7_relat_1('#skF_4','#skF_3'),'#skF_3','#skF_2')
    | k1_relat_1(k7_relat_1('#skF_4','#skF_3')) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1635,c_1959])).

tff(c_1971,plain,(
    k1_relat_1(k7_relat_1('#skF_4','#skF_3')) != '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_1642,c_84,c_1970])).

tff(c_1980,plain,(
    ~ r1_tarski('#skF_3','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1839,c_1971])).

tff(c_1984,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_1980])).

tff(c_1985,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_1990,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1985,c_2])).

tff(c_1986,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_1995,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1985,c_1986])).

tff(c_2017,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1995,c_68])).

tff(c_3555,plain,(
    ! [C_401,A_402,B_403] :
      ( v1_xboole_0(C_401)
      | ~ m1_subset_1(C_401,k1_zfmisc_1(k2_zfmisc_1(A_402,B_403)))
      | ~ v1_xboole_0(A_402) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_3561,plain,
    ( v1_xboole_0('#skF_4')
    | ~ v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_2017,c_3555])).

tff(c_3567,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1990,c_3561])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_2010,plain,(
    ! [A_1] :
      ( A_1 = '#skF_1'
      | ~ v1_xboole_0(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1985,c_4])).

tff(c_3571,plain,(
    '#skF_1' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_3567,c_2010])).

tff(c_2000,plain,(
    v1_funct_2('#skF_4','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1995,c_70])).

tff(c_3603,plain,(
    v1_funct_2('#skF_4','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3571,c_3571,c_2000])).

tff(c_2018,plain,(
    ! [C_247,A_248,B_249] :
      ( v1_relat_1(C_247)
      | ~ m1_subset_1(C_247,k1_zfmisc_1(k2_zfmisc_1(A_248,B_249))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_2022,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_2017,c_2018])).

tff(c_2840,plain,(
    ! [C_337,A_338,B_339] :
      ( v1_xboole_0(C_337)
      | ~ m1_subset_1(C_337,k1_zfmisc_1(k2_zfmisc_1(A_338,B_339)))
      | ~ v1_xboole_0(A_338) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_2843,plain,
    ( v1_xboole_0('#skF_4')
    | ~ v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_2017,c_2840])).

tff(c_2846,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1990,c_2843])).

tff(c_2850,plain,(
    '#skF_1' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_2846,c_2010])).

tff(c_12,plain,(
    ! [A_4] : r1_tarski(k1_xboole_0,A_4) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_1987,plain,(
    ! [A_4] : r1_tarski('#skF_1',A_4) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1985,c_12])).

tff(c_2864,plain,(
    ! [A_4] : r1_tarski('#skF_4',A_4) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2850,c_1987])).

tff(c_18,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_1988,plain,(
    k2_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1985,c_1985,c_18])).

tff(c_2865,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2850,c_2850,c_1988])).

tff(c_20,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_1989,plain,(
    k1_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1985,c_1985,c_20])).

tff(c_2863,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2850,c_2850,c_1989])).

tff(c_3186,plain,(
    ! [B_371,A_372] :
      ( m1_subset_1(B_371,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_371),A_372)))
      | ~ r1_tarski(k2_relat_1(B_371),A_372)
      | ~ v1_funct_1(B_371)
      | ~ v1_relat_1(B_371) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_3220,plain,(
    ! [A_372] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_4',A_372)))
      | ~ r1_tarski(k2_relat_1('#skF_4'),A_372)
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2863,c_3186])).

tff(c_3232,plain,(
    ! [A_372] : m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_4',A_372))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2022,c_72,c_2864,c_2865,c_3220])).

tff(c_2712,plain,(
    ! [C_326,A_327,B_328] :
      ( v1_xboole_0(C_326)
      | ~ m1_subset_1(C_326,k1_zfmisc_1(k2_zfmisc_1(A_327,B_328)))
      | ~ v1_xboole_0(A_327) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_2715,plain,
    ( v1_xboole_0('#skF_4')
    | ~ v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_2017,c_2712])).

tff(c_2718,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1990,c_2715])).

tff(c_2722,plain,(
    '#skF_1' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_2718,c_2010])).

tff(c_2621,plain,(
    ! [B_316,A_317] :
      ( v5_relat_1(B_316,A_317)
      | ~ r1_tarski(k2_relat_1(B_316),A_317)
      | ~ v1_relat_1(B_316) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_2624,plain,(
    ! [A_317] :
      ( v5_relat_1('#skF_1',A_317)
      | ~ r1_tarski('#skF_1',A_317)
      | ~ v1_relat_1('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1988,c_2621])).

tff(c_2630,plain,(
    ! [A_317] :
      ( v5_relat_1('#skF_1',A_317)
      | ~ v1_relat_1('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1987,c_2624])).

tff(c_2649,plain,(
    ~ v1_relat_1('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_2630])).

tff(c_2726,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2722,c_2649])).

tff(c_2742,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2022,c_2726])).

tff(c_2744,plain,(
    v1_relat_1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_2630])).

tff(c_2794,plain,(
    ! [B_333,A_334] :
      ( k7_relat_1(B_333,A_334) = B_333
      | ~ r1_tarski(k1_relat_1(B_333),A_334)
      | ~ v1_relat_1(B_333) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_2797,plain,(
    ! [A_334] :
      ( k7_relat_1('#skF_1',A_334) = '#skF_1'
      | ~ r1_tarski('#skF_1',A_334)
      | ~ v1_relat_1('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1989,c_2794])).

tff(c_2803,plain,(
    ! [A_334] : k7_relat_1('#skF_1',A_334) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2744,c_1987,c_2797])).

tff(c_2851,plain,(
    ! [A_334] : k7_relat_1('#skF_4',A_334) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2850,c_2850,c_2803])).

tff(c_2861,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2850,c_2850,c_2017])).

tff(c_3233,plain,(
    ! [A_373,B_374,C_375,D_376] :
      ( k2_partfun1(A_373,B_374,C_375,D_376) = k7_relat_1(C_375,D_376)
      | ~ m1_subset_1(C_375,k1_zfmisc_1(k2_zfmisc_1(A_373,B_374)))
      | ~ v1_funct_1(C_375) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_3237,plain,(
    ! [D_376] :
      ( k2_partfun1('#skF_4','#skF_4','#skF_4',D_376) = k7_relat_1('#skF_4',D_376)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_2861,c_3233])).

tff(c_3241,plain,(
    ! [D_376] : k2_partfun1('#skF_4','#skF_4','#skF_4',D_376) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_2851,c_3237])).

tff(c_2023,plain,(
    ! [B_250,A_251] :
      ( B_250 = A_251
      | ~ r1_tarski(B_250,A_251)
      | ~ r1_tarski(A_251,B_250) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_2029,plain,
    ( '#skF_3' = '#skF_1'
    | ~ r1_tarski('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_2023])).

tff(c_2037,plain,(
    '#skF_3' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1987,c_2029])).

tff(c_2247,plain,(
    ! [C_281,A_282,B_283] :
      ( v1_xboole_0(C_281)
      | ~ m1_subset_1(C_281,k1_zfmisc_1(k2_zfmisc_1(A_282,B_283)))
      | ~ v1_xboole_0(A_282) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_2250,plain,
    ( v1_xboole_0('#skF_4')
    | ~ v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_2017,c_2247])).

tff(c_2253,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1990,c_2250])).

tff(c_2257,plain,(
    '#skF_1' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_2253,c_2010])).

tff(c_2266,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2257,c_2257,c_2017])).

tff(c_2578,plain,(
    ! [A_305,B_306,C_307,D_308] :
      ( v1_funct_1(k2_partfun1(A_305,B_306,C_307,D_308))
      | ~ m1_subset_1(C_307,k1_zfmisc_1(k2_zfmisc_1(A_305,B_306)))
      | ~ v1_funct_1(C_307) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_2580,plain,(
    ! [D_308] :
      ( v1_funct_1(k2_partfun1('#skF_4','#skF_4','#skF_4',D_308))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_2266,c_2578])).

tff(c_2583,plain,(
    ! [D_308] : v1_funct_1(k2_partfun1('#skF_4','#skF_4','#skF_4',D_308)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_2580])).

tff(c_2038,plain,
    ( ~ m1_subset_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1')))
    | ~ v1_funct_2(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_3'),'#skF_3','#skF_1')
    | ~ v1_funct_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1995,c_1995,c_1995,c_1995,c_1995,c_62])).

tff(c_2039,plain,(
    ~ v1_funct_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_2038])).

tff(c_2059,plain,(
    ~ v1_funct_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2037,c_2039])).

tff(c_2263,plain,(
    ~ v1_funct_1(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2257,c_2257,c_2257,c_2059])).

tff(c_2586,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2583,c_2263])).

tff(c_2587,plain,
    ( ~ v1_funct_2(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_3'),'#skF_3','#skF_1')
    | ~ m1_subset_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_2038])).

tff(c_2609,plain,
    ( ~ v1_funct_2(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),'#skF_1','#skF_1')
    | ~ m1_subset_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2037,c_2037,c_2037,c_2037,c_2587])).

tff(c_2610,plain,(
    ~ m1_subset_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_2609])).

tff(c_2855,plain,(
    ~ m1_subset_1(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2850,c_2850,c_2850,c_2850,c_2850,c_2610])).

tff(c_3316,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3241,c_2855])).

tff(c_3320,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3232,c_3316])).

tff(c_3322,plain,(
    m1_subset_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_2609])).

tff(c_3558,plain,
    ( v1_xboole_0(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'))
    | ~ v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_3322,c_3555])).

tff(c_3564,plain,(
    v1_xboole_0(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1990,c_3558])).

tff(c_3733,plain,(
    v1_xboole_0(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3571,c_3571,c_3571,c_3564])).

tff(c_3598,plain,(
    ! [A_1] :
      ( A_1 = '#skF_4'
      | ~ v1_xboole_0(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3571,c_2010])).

tff(c_3737,plain,(
    k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_3733,c_3598])).

tff(c_3321,plain,(
    ~ v1_funct_2(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),'#skF_1','#skF_1') ),
    inference(splitRight,[status(thm)],[c_2609])).

tff(c_3593,plain,(
    ~ v1_funct_2(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4'),'#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3571,c_3571,c_3571,c_3571,c_3571,c_3321])).

tff(c_3759,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3603,c_3737,c_3593])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 11:33:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.73/1.83  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.84/1.85  
% 4.84/1.85  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.84/1.86  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_partfun1 > k1_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 4.84/1.86  
% 4.84/1.86  %Foreground sorts:
% 4.84/1.86  
% 4.84/1.86  
% 4.84/1.86  %Background operators:
% 4.84/1.86  
% 4.84/1.86  
% 4.84/1.86  %Foreground operators:
% 4.84/1.86  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.84/1.86  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.84/1.86  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 4.84/1.86  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.84/1.86  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.84/1.86  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.84/1.86  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.84/1.86  tff('#skF_2', type, '#skF_2': $i).
% 4.84/1.86  tff('#skF_3', type, '#skF_3': $i).
% 4.84/1.86  tff('#skF_1', type, '#skF_1': $i).
% 4.84/1.86  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 4.84/1.86  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 4.84/1.86  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.84/1.86  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.84/1.86  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.84/1.86  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.84/1.86  tff('#skF_4', type, '#skF_4': $i).
% 4.84/1.86  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.84/1.86  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 4.84/1.86  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 4.84/1.86  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.84/1.86  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.84/1.86  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.84/1.86  
% 4.84/1.88  tff(f_152, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_tarski(C, A) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | ((v1_funct_1(k2_partfun1(A, B, D, C)) & v1_funct_2(k2_partfun1(A, B, D, C), C, B)) & m1_subset_1(k2_partfun1(A, B, D, C), k1_zfmisc_1(k2_zfmisc_1(C, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_funct_2)).
% 4.84/1.88  tff(f_63, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 4.84/1.88  tff(f_80, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 4.84/1.88  tff(f_106, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 4.84/1.88  tff(f_53, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => (k1_relat_1(k7_relat_1(B, A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_relat_1)).
% 4.84/1.88  tff(f_120, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 4.84/1.88  tff(f_36, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.84/1.88  tff(f_114, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (v1_funct_1(k2_partfun1(A, B, C, D)) & m1_subset_1(k2_partfun1(A, B, C, D), k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_partfun1)).
% 4.84/1.88  tff(f_69, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 4.84/1.88  tff(f_88, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_relset_1)).
% 4.84/1.88  tff(f_44, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 4.84/1.88  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 4.84/1.88  tff(f_76, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_xboole_0(C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc3_relset_1)).
% 4.84/1.88  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 4.84/1.88  tff(f_38, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 4.84/1.88  tff(f_47, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 4.84/1.88  tff(f_132, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(k2_relat_1(B), A) => ((v1_funct_1(B) & v1_funct_2(B, k1_relat_1(B), A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B), A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_funct_2)).
% 4.84/1.88  tff(f_59, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t97_relat_1)).
% 4.84/1.88  tff(c_66, plain, (r1_tarski('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_152])).
% 4.84/1.88  tff(c_68, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_152])).
% 4.84/1.88  tff(c_118, plain, (![C_46, A_47, B_48]: (v1_relat_1(C_46) | ~m1_subset_1(C_46, k1_zfmisc_1(k2_zfmisc_1(A_47, B_48))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.84/1.88  tff(c_122, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_68, c_118])).
% 4.84/1.88  tff(c_64, plain, (k1_xboole_0='#skF_1' | k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_152])).
% 4.84/1.88  tff(c_84, plain, (k1_xboole_0!='#skF_2'), inference(splitLeft, [status(thm)], [c_64])).
% 4.84/1.88  tff(c_70, plain, (v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_152])).
% 4.84/1.88  tff(c_1434, plain, (![A_191, B_192, C_193]: (k1_relset_1(A_191, B_192, C_193)=k1_relat_1(C_193) | ~m1_subset_1(C_193, k1_zfmisc_1(k2_zfmisc_1(A_191, B_192))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 4.84/1.88  tff(c_1442, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_68, c_1434])).
% 4.84/1.88  tff(c_1778, plain, (![B_235, A_236, C_237]: (k1_xboole_0=B_235 | k1_relset_1(A_236, B_235, C_237)=A_236 | ~v1_funct_2(C_237, A_236, B_235) | ~m1_subset_1(C_237, k1_zfmisc_1(k2_zfmisc_1(A_236, B_235))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 4.84/1.88  tff(c_1790, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_1' | ~v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_68, c_1778])).
% 4.84/1.88  tff(c_1798, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_1442, c_1790])).
% 4.84/1.88  tff(c_1799, plain, (k1_relat_1('#skF_4')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_84, c_1798])).
% 4.84/1.88  tff(c_22, plain, (![B_8, A_7]: (k1_relat_1(k7_relat_1(B_8, A_7))=A_7 | ~r1_tarski(A_7, k1_relat_1(B_8)) | ~v1_relat_1(B_8))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.84/1.88  tff(c_1819, plain, (![A_7]: (k1_relat_1(k7_relat_1('#skF_4', A_7))=A_7 | ~r1_tarski(A_7, '#skF_1') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1799, c_22])).
% 4.84/1.88  tff(c_1839, plain, (![A_7]: (k1_relat_1(k7_relat_1('#skF_4', A_7))=A_7 | ~r1_tarski(A_7, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_122, c_1819])).
% 4.84/1.88  tff(c_72, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_152])).
% 4.84/1.88  tff(c_1621, plain, (![A_222, B_223, C_224, D_225]: (k2_partfun1(A_222, B_223, C_224, D_225)=k7_relat_1(C_224, D_225) | ~m1_subset_1(C_224, k1_zfmisc_1(k2_zfmisc_1(A_222, B_223))) | ~v1_funct_1(C_224))), inference(cnfTransformation, [status(thm)], [f_120])).
% 4.84/1.88  tff(c_1627, plain, (![D_225]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_225)=k7_relat_1('#skF_4', D_225) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_68, c_1621])).
% 4.84/1.88  tff(c_1634, plain, (![D_225]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_225)=k7_relat_1('#skF_4', D_225))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_1627])).
% 4.84/1.88  tff(c_10, plain, (![B_3]: (r1_tarski(B_3, B_3))), inference(cnfTransformation, [status(thm)], [f_36])).
% 4.84/1.88  tff(c_409, plain, (![A_105, B_106, C_107]: (k1_relset_1(A_105, B_106, C_107)=k1_relat_1(C_107) | ~m1_subset_1(C_107, k1_zfmisc_1(k2_zfmisc_1(A_105, B_106))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 4.84/1.88  tff(c_413, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_68, c_409])).
% 4.84/1.88  tff(c_737, plain, (![B_154, A_155, C_156]: (k1_xboole_0=B_154 | k1_relset_1(A_155, B_154, C_156)=A_155 | ~v1_funct_2(C_156, A_155, B_154) | ~m1_subset_1(C_156, k1_zfmisc_1(k2_zfmisc_1(A_155, B_154))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 4.84/1.88  tff(c_746, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_1' | ~v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_68, c_737])).
% 4.84/1.88  tff(c_751, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_413, c_746])).
% 4.84/1.88  tff(c_752, plain, (k1_relat_1('#skF_4')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_84, c_751])).
% 4.84/1.88  tff(c_775, plain, (![A_7]: (k1_relat_1(k7_relat_1('#skF_4', A_7))=A_7 | ~r1_tarski(A_7, '#skF_1') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_752, c_22])).
% 4.84/1.88  tff(c_797, plain, (![A_7]: (k1_relat_1(k7_relat_1('#skF_4', A_7))=A_7 | ~r1_tarski(A_7, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_122, c_775])).
% 4.84/1.88  tff(c_616, plain, (![A_137, B_138, C_139, D_140]: (k2_partfun1(A_137, B_138, C_139, D_140)=k7_relat_1(C_139, D_140) | ~m1_subset_1(C_139, k1_zfmisc_1(k2_zfmisc_1(A_137, B_138))) | ~v1_funct_1(C_139))), inference(cnfTransformation, [status(thm)], [f_120])).
% 4.84/1.88  tff(c_620, plain, (![D_140]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_140)=k7_relat_1('#skF_4', D_140) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_68, c_616])).
% 4.84/1.88  tff(c_624, plain, (![D_140]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_140)=k7_relat_1('#skF_4', D_140))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_620])).
% 4.84/1.88  tff(c_1164, plain, (![A_175, B_176, C_177, D_178]: (m1_subset_1(k2_partfun1(A_175, B_176, C_177, D_178), k1_zfmisc_1(k2_zfmisc_1(A_175, B_176))) | ~m1_subset_1(C_177, k1_zfmisc_1(k2_zfmisc_1(A_175, B_176))) | ~v1_funct_1(C_177))), inference(cnfTransformation, [status(thm)], [f_114])).
% 4.84/1.88  tff(c_1204, plain, (![D_140]: (m1_subset_1(k7_relat_1('#skF_4', D_140), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_624, c_1164])).
% 4.84/1.88  tff(c_1219, plain, (![D_179]: (m1_subset_1(k7_relat_1('#skF_4', D_179), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_68, c_1204])).
% 4.84/1.88  tff(c_28, plain, (![C_16, B_15, A_14]: (v5_relat_1(C_16, B_15) | ~m1_subset_1(C_16, k1_zfmisc_1(k2_zfmisc_1(A_14, B_15))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.84/1.88  tff(c_1265, plain, (![D_179]: (v5_relat_1(k7_relat_1('#skF_4', D_179), '#skF_2'))), inference(resolution, [status(thm)], [c_1219, c_28])).
% 4.84/1.88  tff(c_1028, plain, (![A_169, B_170, C_171, D_172]: (m1_subset_1(k2_partfun1(A_169, B_170, C_171, D_172), k1_zfmisc_1(k2_zfmisc_1(A_169, B_170))) | ~m1_subset_1(C_171, k1_zfmisc_1(k2_zfmisc_1(A_169, B_170))) | ~v1_funct_1(C_171))), inference(cnfTransformation, [status(thm)], [f_114])).
% 4.84/1.88  tff(c_1068, plain, (![D_140]: (m1_subset_1(k7_relat_1('#skF_4', D_140), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_624, c_1028])).
% 4.84/1.88  tff(c_1083, plain, (![D_173]: (m1_subset_1(k7_relat_1('#skF_4', D_173), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_68, c_1068])).
% 4.84/1.88  tff(c_26, plain, (![C_13, A_11, B_12]: (v1_relat_1(C_13) | ~m1_subset_1(C_13, k1_zfmisc_1(k2_zfmisc_1(A_11, B_12))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.84/1.88  tff(c_1131, plain, (![D_173]: (v1_relat_1(k7_relat_1('#skF_4', D_173)))), inference(resolution, [status(thm)], [c_1083, c_26])).
% 4.84/1.88  tff(c_643, plain, (![C_143, A_144, B_145]: (m1_subset_1(C_143, k1_zfmisc_1(k2_zfmisc_1(A_144, B_145))) | ~r1_tarski(k2_relat_1(C_143), B_145) | ~r1_tarski(k1_relat_1(C_143), A_144) | ~v1_relat_1(C_143))), inference(cnfTransformation, [status(thm)], [f_88])).
% 4.84/1.88  tff(c_315, plain, (![A_81, B_82, C_83, D_84]: (v1_funct_1(k2_partfun1(A_81, B_82, C_83, D_84)) | ~m1_subset_1(C_83, k1_zfmisc_1(k2_zfmisc_1(A_81, B_82))) | ~v1_funct_1(C_83))), inference(cnfTransformation, [status(thm)], [f_114])).
% 4.84/1.88  tff(c_317, plain, (![D_84]: (v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_84)) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_68, c_315])).
% 4.84/1.88  tff(c_320, plain, (![D_84]: (v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_84)))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_317])).
% 4.84/1.88  tff(c_62, plain, (~m1_subset_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_2(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_3', '#skF_2') | ~v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_152])).
% 4.84/1.88  tff(c_134, plain, (~v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))), inference(splitLeft, [status(thm)], [c_62])).
% 4.84/1.88  tff(c_324, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_320, c_134])).
% 4.84/1.88  tff(c_325, plain, (~v1_funct_2(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_3', '#skF_2') | ~m1_subset_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitRight, [status(thm)], [c_62])).
% 4.84/1.88  tff(c_383, plain, (~m1_subset_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitLeft, [status(thm)], [c_325])).
% 4.84/1.88  tff(c_626, plain, (~m1_subset_1(k7_relat_1('#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_624, c_383])).
% 4.84/1.88  tff(c_682, plain, (~r1_tarski(k2_relat_1(k7_relat_1('#skF_4', '#skF_3')), '#skF_2') | ~r1_tarski(k1_relat_1(k7_relat_1('#skF_4', '#skF_3')), '#skF_3') | ~v1_relat_1(k7_relat_1('#skF_4', '#skF_3'))), inference(resolution, [status(thm)], [c_643, c_626])).
% 4.84/1.88  tff(c_992, plain, (~v1_relat_1(k7_relat_1('#skF_4', '#skF_3'))), inference(splitLeft, [status(thm)], [c_682])).
% 4.84/1.88  tff(c_1137, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1131, c_992])).
% 4.84/1.88  tff(c_1139, plain, (v1_relat_1(k7_relat_1('#skF_4', '#skF_3'))), inference(splitRight, [status(thm)], [c_682])).
% 4.84/1.88  tff(c_16, plain, (![B_6, A_5]: (r1_tarski(k2_relat_1(B_6), A_5) | ~v5_relat_1(B_6, A_5) | ~v1_relat_1(B_6))), inference(cnfTransformation, [status(thm)], [f_44])).
% 4.84/1.88  tff(c_1138, plain, (~r1_tarski(k1_relat_1(k7_relat_1('#skF_4', '#skF_3')), '#skF_3') | ~r1_tarski(k2_relat_1(k7_relat_1('#skF_4', '#skF_3')), '#skF_2')), inference(splitRight, [status(thm)], [c_682])).
% 4.84/1.88  tff(c_1140, plain, (~r1_tarski(k2_relat_1(k7_relat_1('#skF_4', '#skF_3')), '#skF_2')), inference(splitLeft, [status(thm)], [c_1138])).
% 4.84/1.88  tff(c_1143, plain, (~v5_relat_1(k7_relat_1('#skF_4', '#skF_3'), '#skF_2') | ~v1_relat_1(k7_relat_1('#skF_4', '#skF_3'))), inference(resolution, [status(thm)], [c_16, c_1140])).
% 4.84/1.88  tff(c_1146, plain, (~v5_relat_1(k7_relat_1('#skF_4', '#skF_3'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1139, c_1143])).
% 4.84/1.88  tff(c_1290, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1265, c_1146])).
% 4.84/1.88  tff(c_1291, plain, (~r1_tarski(k1_relat_1(k7_relat_1('#skF_4', '#skF_3')), '#skF_3')), inference(splitRight, [status(thm)], [c_1138])).
% 4.84/1.88  tff(c_1366, plain, (~r1_tarski('#skF_3', '#skF_3') | ~r1_tarski('#skF_3', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_797, c_1291])).
% 4.84/1.88  tff(c_1369, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_66, c_10, c_1366])).
% 4.84/1.88  tff(c_1370, plain, (~v1_funct_2(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_325])).
% 4.84/1.88  tff(c_1642, plain, (~v1_funct_2(k7_relat_1('#skF_4', '#skF_3'), '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1634, c_1370])).
% 4.84/1.88  tff(c_1371, plain, (m1_subset_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitRight, [status(thm)], [c_325])).
% 4.84/1.88  tff(c_1441, plain, (k1_relset_1('#skF_3', '#skF_2', k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))=k1_relat_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))), inference(resolution, [status(thm)], [c_1371, c_1434])).
% 4.84/1.88  tff(c_1635, plain, (k1_relset_1('#skF_3', '#skF_2', k7_relat_1('#skF_4', '#skF_3'))=k1_relat_1(k7_relat_1('#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1634, c_1634, c_1441])).
% 4.84/1.88  tff(c_1641, plain, (m1_subset_1(k7_relat_1('#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_1634, c_1371])).
% 4.84/1.88  tff(c_1956, plain, (![B_242, C_243, A_244]: (k1_xboole_0=B_242 | v1_funct_2(C_243, A_244, B_242) | k1_relset_1(A_244, B_242, C_243)!=A_244 | ~m1_subset_1(C_243, k1_zfmisc_1(k2_zfmisc_1(A_244, B_242))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 4.84/1.88  tff(c_1959, plain, (k1_xboole_0='#skF_2' | v1_funct_2(k7_relat_1('#skF_4', '#skF_3'), '#skF_3', '#skF_2') | k1_relset_1('#skF_3', '#skF_2', k7_relat_1('#skF_4', '#skF_3'))!='#skF_3'), inference(resolution, [status(thm)], [c_1641, c_1956])).
% 4.84/1.88  tff(c_1970, plain, (k1_xboole_0='#skF_2' | v1_funct_2(k7_relat_1('#skF_4', '#skF_3'), '#skF_3', '#skF_2') | k1_relat_1(k7_relat_1('#skF_4', '#skF_3'))!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1635, c_1959])).
% 4.84/1.88  tff(c_1971, plain, (k1_relat_1(k7_relat_1('#skF_4', '#skF_3'))!='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_1642, c_84, c_1970])).
% 4.84/1.88  tff(c_1980, plain, (~r1_tarski('#skF_3', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1839, c_1971])).
% 4.84/1.88  tff(c_1984, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_66, c_1980])).
% 4.84/1.88  tff(c_1985, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_64])).
% 4.84/1.88  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 4.84/1.88  tff(c_1990, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1985, c_2])).
% 4.84/1.88  tff(c_1986, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_64])).
% 4.84/1.88  tff(c_1995, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1985, c_1986])).
% 4.84/1.88  tff(c_2017, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_1995, c_68])).
% 4.84/1.88  tff(c_3555, plain, (![C_401, A_402, B_403]: (v1_xboole_0(C_401) | ~m1_subset_1(C_401, k1_zfmisc_1(k2_zfmisc_1(A_402, B_403))) | ~v1_xboole_0(A_402))), inference(cnfTransformation, [status(thm)], [f_76])).
% 4.84/1.88  tff(c_3561, plain, (v1_xboole_0('#skF_4') | ~v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_2017, c_3555])).
% 4.84/1.88  tff(c_3567, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1990, c_3561])).
% 4.84/1.88  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 4.84/1.88  tff(c_2010, plain, (![A_1]: (A_1='#skF_1' | ~v1_xboole_0(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_1985, c_4])).
% 4.84/1.88  tff(c_3571, plain, ('#skF_1'='#skF_4'), inference(resolution, [status(thm)], [c_3567, c_2010])).
% 4.84/1.88  tff(c_2000, plain, (v1_funct_2('#skF_4', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1995, c_70])).
% 4.84/1.88  tff(c_3603, plain, (v1_funct_2('#skF_4', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_3571, c_3571, c_2000])).
% 4.84/1.88  tff(c_2018, plain, (![C_247, A_248, B_249]: (v1_relat_1(C_247) | ~m1_subset_1(C_247, k1_zfmisc_1(k2_zfmisc_1(A_248, B_249))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.84/1.88  tff(c_2022, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_2017, c_2018])).
% 4.84/1.88  tff(c_2840, plain, (![C_337, A_338, B_339]: (v1_xboole_0(C_337) | ~m1_subset_1(C_337, k1_zfmisc_1(k2_zfmisc_1(A_338, B_339))) | ~v1_xboole_0(A_338))), inference(cnfTransformation, [status(thm)], [f_76])).
% 4.84/1.88  tff(c_2843, plain, (v1_xboole_0('#skF_4') | ~v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_2017, c_2840])).
% 4.84/1.88  tff(c_2846, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1990, c_2843])).
% 4.84/1.88  tff(c_2850, plain, ('#skF_1'='#skF_4'), inference(resolution, [status(thm)], [c_2846, c_2010])).
% 4.84/1.88  tff(c_12, plain, (![A_4]: (r1_tarski(k1_xboole_0, A_4))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.84/1.88  tff(c_1987, plain, (![A_4]: (r1_tarski('#skF_1', A_4))), inference(demodulation, [status(thm), theory('equality')], [c_1985, c_12])).
% 4.84/1.88  tff(c_2864, plain, (![A_4]: (r1_tarski('#skF_4', A_4))), inference(demodulation, [status(thm), theory('equality')], [c_2850, c_1987])).
% 4.84/1.88  tff(c_18, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.84/1.88  tff(c_1988, plain, (k2_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1985, c_1985, c_18])).
% 4.84/1.88  tff(c_2865, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_2850, c_2850, c_1988])).
% 4.84/1.88  tff(c_20, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.84/1.88  tff(c_1989, plain, (k1_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1985, c_1985, c_20])).
% 4.84/1.88  tff(c_2863, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_2850, c_2850, c_1989])).
% 4.84/1.88  tff(c_3186, plain, (![B_371, A_372]: (m1_subset_1(B_371, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_371), A_372))) | ~r1_tarski(k2_relat_1(B_371), A_372) | ~v1_funct_1(B_371) | ~v1_relat_1(B_371))), inference(cnfTransformation, [status(thm)], [f_132])).
% 4.84/1.88  tff(c_3220, plain, (![A_372]: (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_4', A_372))) | ~r1_tarski(k2_relat_1('#skF_4'), A_372) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_2863, c_3186])).
% 4.84/1.88  tff(c_3232, plain, (![A_372]: (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_4', A_372))))), inference(demodulation, [status(thm), theory('equality')], [c_2022, c_72, c_2864, c_2865, c_3220])).
% 4.84/1.88  tff(c_2712, plain, (![C_326, A_327, B_328]: (v1_xboole_0(C_326) | ~m1_subset_1(C_326, k1_zfmisc_1(k2_zfmisc_1(A_327, B_328))) | ~v1_xboole_0(A_327))), inference(cnfTransformation, [status(thm)], [f_76])).
% 4.84/1.88  tff(c_2715, plain, (v1_xboole_0('#skF_4') | ~v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_2017, c_2712])).
% 4.84/1.88  tff(c_2718, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1990, c_2715])).
% 4.84/1.88  tff(c_2722, plain, ('#skF_1'='#skF_4'), inference(resolution, [status(thm)], [c_2718, c_2010])).
% 4.84/1.88  tff(c_2621, plain, (![B_316, A_317]: (v5_relat_1(B_316, A_317) | ~r1_tarski(k2_relat_1(B_316), A_317) | ~v1_relat_1(B_316))), inference(cnfTransformation, [status(thm)], [f_44])).
% 4.84/1.88  tff(c_2624, plain, (![A_317]: (v5_relat_1('#skF_1', A_317) | ~r1_tarski('#skF_1', A_317) | ~v1_relat_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_1988, c_2621])).
% 4.84/1.88  tff(c_2630, plain, (![A_317]: (v5_relat_1('#skF_1', A_317) | ~v1_relat_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_1987, c_2624])).
% 4.84/1.88  tff(c_2649, plain, (~v1_relat_1('#skF_1')), inference(splitLeft, [status(thm)], [c_2630])).
% 4.84/1.88  tff(c_2726, plain, (~v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2722, c_2649])).
% 4.84/1.88  tff(c_2742, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2022, c_2726])).
% 4.84/1.88  tff(c_2744, plain, (v1_relat_1('#skF_1')), inference(splitRight, [status(thm)], [c_2630])).
% 4.84/1.88  tff(c_2794, plain, (![B_333, A_334]: (k7_relat_1(B_333, A_334)=B_333 | ~r1_tarski(k1_relat_1(B_333), A_334) | ~v1_relat_1(B_333))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.84/1.88  tff(c_2797, plain, (![A_334]: (k7_relat_1('#skF_1', A_334)='#skF_1' | ~r1_tarski('#skF_1', A_334) | ~v1_relat_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_1989, c_2794])).
% 4.84/1.88  tff(c_2803, plain, (![A_334]: (k7_relat_1('#skF_1', A_334)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2744, c_1987, c_2797])).
% 4.84/1.88  tff(c_2851, plain, (![A_334]: (k7_relat_1('#skF_4', A_334)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2850, c_2850, c_2803])).
% 4.84/1.88  tff(c_2861, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_2850, c_2850, c_2017])).
% 4.84/1.88  tff(c_3233, plain, (![A_373, B_374, C_375, D_376]: (k2_partfun1(A_373, B_374, C_375, D_376)=k7_relat_1(C_375, D_376) | ~m1_subset_1(C_375, k1_zfmisc_1(k2_zfmisc_1(A_373, B_374))) | ~v1_funct_1(C_375))), inference(cnfTransformation, [status(thm)], [f_120])).
% 4.84/1.88  tff(c_3237, plain, (![D_376]: (k2_partfun1('#skF_4', '#skF_4', '#skF_4', D_376)=k7_relat_1('#skF_4', D_376) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_2861, c_3233])).
% 4.84/1.88  tff(c_3241, plain, (![D_376]: (k2_partfun1('#skF_4', '#skF_4', '#skF_4', D_376)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_2851, c_3237])).
% 4.84/1.88  tff(c_2023, plain, (![B_250, A_251]: (B_250=A_251 | ~r1_tarski(B_250, A_251) | ~r1_tarski(A_251, B_250))), inference(cnfTransformation, [status(thm)], [f_36])).
% 4.84/1.88  tff(c_2029, plain, ('#skF_3'='#skF_1' | ~r1_tarski('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_66, c_2023])).
% 4.84/1.88  tff(c_2037, plain, ('#skF_3'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1987, c_2029])).
% 4.84/1.88  tff(c_2247, plain, (![C_281, A_282, B_283]: (v1_xboole_0(C_281) | ~m1_subset_1(C_281, k1_zfmisc_1(k2_zfmisc_1(A_282, B_283))) | ~v1_xboole_0(A_282))), inference(cnfTransformation, [status(thm)], [f_76])).
% 4.84/1.88  tff(c_2250, plain, (v1_xboole_0('#skF_4') | ~v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_2017, c_2247])).
% 4.84/1.88  tff(c_2253, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1990, c_2250])).
% 4.84/1.88  tff(c_2257, plain, ('#skF_1'='#skF_4'), inference(resolution, [status(thm)], [c_2253, c_2010])).
% 4.84/1.88  tff(c_2266, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_2257, c_2257, c_2017])).
% 4.84/1.88  tff(c_2578, plain, (![A_305, B_306, C_307, D_308]: (v1_funct_1(k2_partfun1(A_305, B_306, C_307, D_308)) | ~m1_subset_1(C_307, k1_zfmisc_1(k2_zfmisc_1(A_305, B_306))) | ~v1_funct_1(C_307))), inference(cnfTransformation, [status(thm)], [f_114])).
% 4.84/1.88  tff(c_2580, plain, (![D_308]: (v1_funct_1(k2_partfun1('#skF_4', '#skF_4', '#skF_4', D_308)) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_2266, c_2578])).
% 4.84/1.88  tff(c_2583, plain, (![D_308]: (v1_funct_1(k2_partfun1('#skF_4', '#skF_4', '#skF_4', D_308)))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_2580])).
% 4.84/1.88  tff(c_2038, plain, (~m1_subset_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1'))) | ~v1_funct_2(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_3'), '#skF_3', '#skF_1') | ~v1_funct_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1995, c_1995, c_1995, c_1995, c_1995, c_62])).
% 4.84/1.88  tff(c_2039, plain, (~v1_funct_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_3'))), inference(splitLeft, [status(thm)], [c_2038])).
% 4.84/1.88  tff(c_2059, plain, (~v1_funct_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_2037, c_2039])).
% 4.84/1.88  tff(c_2263, plain, (~v1_funct_1(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_2257, c_2257, c_2257, c_2059])).
% 4.84/1.88  tff(c_2586, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2583, c_2263])).
% 4.84/1.88  tff(c_2587, plain, (~v1_funct_2(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_3'), '#skF_3', '#skF_1') | ~m1_subset_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1')))), inference(splitRight, [status(thm)], [c_2038])).
% 4.84/1.88  tff(c_2609, plain, (~v1_funct_2(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), '#skF_1', '#skF_1') | ~m1_subset_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_2037, c_2037, c_2037, c_2037, c_2587])).
% 4.84/1.88  tff(c_2610, plain, (~m1_subset_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_2609])).
% 4.84/1.89  tff(c_2855, plain, (~m1_subset_1(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_2850, c_2850, c_2850, c_2850, c_2850, c_2610])).
% 4.84/1.89  tff(c_3316, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_3241, c_2855])).
% 4.84/1.89  tff(c_3320, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3232, c_3316])).
% 4.84/1.89  tff(c_3322, plain, (m1_subset_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitRight, [status(thm)], [c_2609])).
% 4.84/1.89  tff(c_3558, plain, (v1_xboole_0(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1')) | ~v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_3322, c_3555])).
% 4.84/1.89  tff(c_3564, plain, (v1_xboole_0(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_1990, c_3558])).
% 4.84/1.89  tff(c_3733, plain, (v1_xboole_0(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_3571, c_3571, c_3571, c_3564])).
% 4.84/1.89  tff(c_3598, plain, (![A_1]: (A_1='#skF_4' | ~v1_xboole_0(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_3571, c_2010])).
% 4.84/1.89  tff(c_3737, plain, (k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_3733, c_3598])).
% 4.84/1.89  tff(c_3321, plain, (~v1_funct_2(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), '#skF_1', '#skF_1')), inference(splitRight, [status(thm)], [c_2609])).
% 4.84/1.89  tff(c_3593, plain, (~v1_funct_2(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'), '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_3571, c_3571, c_3571, c_3571, c_3571, c_3321])).
% 4.84/1.89  tff(c_3759, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3603, c_3737, c_3593])).
% 4.84/1.89  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.84/1.89  
% 4.84/1.89  Inference rules
% 4.84/1.89  ----------------------
% 4.84/1.89  #Ref     : 0
% 4.84/1.89  #Sup     : 763
% 4.84/1.89  #Fact    : 0
% 4.84/1.89  #Define  : 0
% 4.84/1.89  #Split   : 18
% 4.84/1.89  #Chain   : 0
% 4.84/1.89  #Close   : 0
% 4.84/1.89  
% 4.84/1.89  Ordering : KBO
% 4.84/1.89  
% 4.84/1.89  Simplification rules
% 4.84/1.89  ----------------------
% 4.84/1.89  #Subsume      : 86
% 4.84/1.89  #Demod        : 790
% 4.84/1.89  #Tautology    : 356
% 4.84/1.89  #SimpNegUnit  : 10
% 4.84/1.89  #BackRed      : 143
% 4.84/1.89  
% 4.84/1.89  #Partial instantiations: 0
% 4.84/1.89  #Strategies tried      : 1
% 4.84/1.89  
% 4.84/1.89  Timing (in seconds)
% 4.84/1.89  ----------------------
% 4.84/1.89  Preprocessing        : 0.35
% 4.84/1.89  Parsing              : 0.19
% 4.84/1.89  CNF conversion       : 0.02
% 4.84/1.89  Main loop            : 0.74
% 4.84/1.89  Inferencing          : 0.26
% 4.84/1.89  Reduction            : 0.25
% 4.84/1.89  Demodulation         : 0.18
% 4.84/1.89  BG Simplification    : 0.03
% 4.84/1.89  Subsumption          : 0.12
% 4.84/1.89  Abstraction          : 0.03
% 4.84/1.89  MUC search           : 0.00
% 4.84/1.89  Cooper               : 0.00
% 4.84/1.89  Total                : 1.15
% 4.84/1.89  Index Insertion      : 0.00
% 4.84/1.89  Index Deletion       : 0.00
% 4.84/1.89  Index Matching       : 0.00
% 4.84/1.89  BG Taut test         : 0.00
%------------------------------------------------------------------------------
