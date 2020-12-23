%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:34 EST 2020

% Result     : Theorem 20.86s
% Output     : CNFRefutation 20.90s
% Verified   : 
% Statistics : Number of formulae       :  211 (1325 expanded)
%              Number of leaves         :   42 ( 414 expanded)
%              Depth                    :   13
%              Number of atoms          :  350 (3965 expanded)
%              Number of equality atoms :   86 (1281 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_partfun1 > k1_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff(f_168,negated_conjecture,(
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

tff(f_87,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_104,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_122,axiom,(
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

tff(f_71,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => k1_relat_1(k7_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).

tff(f_136,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_130,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( v1_funct_1(k2_partfun1(A,B,C,D))
        & m1_subset_1(k2_partfun1(A,B,C,D),k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_partfun1)).

tff(f_93,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_148,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(k2_relat_1(B),A)
       => ( v1_funct_1(B)
          & v1_funct_2(B,k1_relat_1(B),A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B),A))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_100,axiom,(
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

tff(f_46,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_65,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_62,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k7_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t110_relat_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).

tff(c_74,plain,(
    r1_tarski('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_76,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_58122,plain,(
    ! [C_1468,A_1469,B_1470] :
      ( v1_relat_1(C_1468)
      | ~ m1_subset_1(C_1468,k1_zfmisc_1(k2_zfmisc_1(A_1469,B_1470))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_58131,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_76,c_58122])).

tff(c_72,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_93,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_72])).

tff(c_78,plain,(
    v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_58615,plain,(
    ! [A_1513,B_1514,C_1515] :
      ( k1_relset_1(A_1513,B_1514,C_1515) = k1_relat_1(C_1515)
      | ~ m1_subset_1(C_1515,k1_zfmisc_1(k2_zfmisc_1(A_1513,B_1514))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_58629,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_76,c_58615])).

tff(c_59067,plain,(
    ! [B_1560,A_1561,C_1562] :
      ( k1_xboole_0 = B_1560
      | k1_relset_1(A_1561,B_1560,C_1562) = A_1561
      | ~ v1_funct_2(C_1562,A_1561,B_1560)
      | ~ m1_subset_1(C_1562,k1_zfmisc_1(k2_zfmisc_1(A_1561,B_1560))) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_59077,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_76,c_59067])).

tff(c_59083,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_58629,c_59077])).

tff(c_59084,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_93,c_59083])).

tff(c_28,plain,(
    ! [B_14,A_13] :
      ( k1_relat_1(k7_relat_1(B_14,A_13)) = A_13
      | ~ r1_tarski(A_13,k1_relat_1(B_14))
      | ~ v1_relat_1(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_59104,plain,(
    ! [A_13] :
      ( k1_relat_1(k7_relat_1('#skF_4',A_13)) = A_13
      | ~ r1_tarski(A_13,'#skF_1')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_59084,c_28])).

tff(c_59118,plain,(
    ! [A_13] :
      ( k1_relat_1(k7_relat_1('#skF_4',A_13)) = A_13
      | ~ r1_tarski(A_13,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58131,c_59104])).

tff(c_80,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_59019,plain,(
    ! [A_1554,B_1555,C_1556,D_1557] :
      ( k2_partfun1(A_1554,B_1555,C_1556,D_1557) = k7_relat_1(C_1556,D_1557)
      | ~ m1_subset_1(C_1556,k1_zfmisc_1(k2_zfmisc_1(A_1554,B_1555)))
      | ~ v1_funct_1(C_1556) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_59028,plain,(
    ! [D_1557] :
      ( k2_partfun1('#skF_1','#skF_2','#skF_4',D_1557) = k7_relat_1('#skF_4',D_1557)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_76,c_59019])).

tff(c_59038,plain,(
    ! [D_1557] : k2_partfun1('#skF_1','#skF_2','#skF_4',D_1557) = k7_relat_1('#skF_4',D_1557) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_59028])).

tff(c_1553,plain,(
    ! [A_206,B_207,C_208,D_209] :
      ( k2_partfun1(A_206,B_207,C_208,D_209) = k7_relat_1(C_208,D_209)
      | ~ m1_subset_1(C_208,k1_zfmisc_1(k2_zfmisc_1(A_206,B_207)))
      | ~ v1_funct_1(C_208) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_1560,plain,(
    ! [D_209] :
      ( k2_partfun1('#skF_1','#skF_2','#skF_4',D_209) = k7_relat_1('#skF_4',D_209)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_76,c_1553])).

tff(c_1567,plain,(
    ! [D_209] : k2_partfun1('#skF_1','#skF_2','#skF_4',D_209) = k7_relat_1('#skF_4',D_209) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_1560])).

tff(c_2148,plain,(
    ! [A_240,B_241,C_242,D_243] :
      ( m1_subset_1(k2_partfun1(A_240,B_241,C_242,D_243),k1_zfmisc_1(k2_zfmisc_1(A_240,B_241)))
      | ~ m1_subset_1(C_242,k1_zfmisc_1(k2_zfmisc_1(A_240,B_241)))
      | ~ v1_funct_1(C_242) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_2193,plain,(
    ! [D_209] :
      ( m1_subset_1(k7_relat_1('#skF_4',D_209),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1567,c_2148])).

tff(c_2211,plain,(
    ! [D_244] : m1_subset_1(k7_relat_1('#skF_4',D_244),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_76,c_2193])).

tff(c_36,plain,(
    ! [C_21,A_19,B_20] :
      ( v1_relat_1(C_21)
      | ~ m1_subset_1(C_21,k1_zfmisc_1(k2_zfmisc_1(A_19,B_20))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_2258,plain,(
    ! [D_244] : v1_relat_1(k7_relat_1('#skF_4',D_244)) ),
    inference(resolution,[status(thm)],[c_2211,c_36])).

tff(c_38,plain,(
    ! [C_24,B_23,A_22] :
      ( v5_relat_1(C_24,B_23)
      | ~ m1_subset_1(C_24,k1_zfmisc_1(k2_zfmisc_1(A_22,B_23))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_2257,plain,(
    ! [D_244] : v5_relat_1(k7_relat_1('#skF_4',D_244),'#skF_2') ),
    inference(resolution,[status(thm)],[c_2211,c_38])).

tff(c_20,plain,(
    ! [B_11,A_10] :
      ( r1_tarski(k2_relat_1(B_11),A_10)
      | ~ v5_relat_1(B_11,A_10)
      | ~ v1_relat_1(B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_1244,plain,(
    ! [A_177,B_178,C_179,D_180] :
      ( v1_funct_1(k2_partfun1(A_177,B_178,C_179,D_180))
      | ~ m1_subset_1(C_179,k1_zfmisc_1(k2_zfmisc_1(A_177,B_178)))
      | ~ v1_funct_1(C_179) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_1249,plain,(
    ! [D_180] :
      ( v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4',D_180))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_76,c_1244])).

tff(c_1255,plain,(
    ! [D_180] : v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4',D_180)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_1249])).

tff(c_1568,plain,(
    ! [D_180] : v1_funct_1(k7_relat_1('#skF_4',D_180)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1567,c_1255])).

tff(c_745,plain,(
    ! [C_122,A_123,B_124] :
      ( v1_relat_1(C_122)
      | ~ m1_subset_1(C_122,k1_zfmisc_1(k2_zfmisc_1(A_123,B_124))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_754,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_76,c_745])).

tff(c_1053,plain,(
    ! [A_162,B_163,C_164] :
      ( k1_relset_1(A_162,B_163,C_164) = k1_relat_1(C_164)
      | ~ m1_subset_1(C_164,k1_zfmisc_1(k2_zfmisc_1(A_162,B_163))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_1063,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_76,c_1053])).

tff(c_1714,plain,(
    ! [B_225,A_226,C_227] :
      ( k1_xboole_0 = B_225
      | k1_relset_1(A_226,B_225,C_227) = A_226
      | ~ v1_funct_2(C_227,A_226,B_225)
      | ~ m1_subset_1(C_227,k1_zfmisc_1(k2_zfmisc_1(A_226,B_225))) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_1724,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_76,c_1714])).

tff(c_1730,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_1063,c_1724])).

tff(c_1731,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_93,c_1730])).

tff(c_1751,plain,(
    ! [A_13] :
      ( k1_relat_1(k7_relat_1('#skF_4',A_13)) = A_13
      | ~ r1_tarski(A_13,'#skF_1')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1731,c_28])).

tff(c_1838,plain,(
    ! [A_232] :
      ( k1_relat_1(k7_relat_1('#skF_4',A_232)) = A_232
      | ~ r1_tarski(A_232,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_754,c_1751])).

tff(c_64,plain,(
    ! [B_44,A_43] :
      ( m1_subset_1(B_44,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_44),A_43)))
      | ~ r1_tarski(k2_relat_1(B_44),A_43)
      | ~ v1_funct_1(B_44)
      | ~ v1_relat_1(B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_1857,plain,(
    ! [A_232,A_43] :
      ( m1_subset_1(k7_relat_1('#skF_4',A_232),k1_zfmisc_1(k2_zfmisc_1(A_232,A_43)))
      | ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_4',A_232)),A_43)
      | ~ v1_funct_1(k7_relat_1('#skF_4',A_232))
      | ~ v1_relat_1(k7_relat_1('#skF_4',A_232))
      | ~ r1_tarski(A_232,'#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1838,c_64])).

tff(c_1908,plain,(
    ! [A_232,A_43] :
      ( m1_subset_1(k7_relat_1('#skF_4',A_232),k1_zfmisc_1(k2_zfmisc_1(A_232,A_43)))
      | ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_4',A_232)),A_43)
      | ~ v1_relat_1(k7_relat_1('#skF_4',A_232))
      | ~ r1_tarski(A_232,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1568,c_1857])).

tff(c_57974,plain,(
    ! [A_1466,A_1467] :
      ( m1_subset_1(k7_relat_1('#skF_4',A_1466),k1_zfmisc_1(k2_zfmisc_1(A_1466,A_1467)))
      | ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_4',A_1466)),A_1467)
      | ~ r1_tarski(A_1466,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2258,c_1908])).

tff(c_727,plain,(
    ! [A_118,B_119,C_120,D_121] :
      ( v1_funct_1(k2_partfun1(A_118,B_119,C_120,D_121))
      | ~ m1_subset_1(C_120,k1_zfmisc_1(k2_zfmisc_1(A_118,B_119)))
      | ~ v1_funct_1(C_120) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_732,plain,(
    ! [D_121] :
      ( v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4',D_121))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_76,c_727])).

tff(c_738,plain,(
    ! [D_121] : v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4',D_121)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_732])).

tff(c_70,plain,
    ( ~ m1_subset_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_2(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_3','#skF_2')
    | ~ v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_124,plain,(
    ~ v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_70])).

tff(c_741,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_738,c_124])).

tff(c_742,plain,
    ( ~ v1_funct_2(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_3','#skF_2')
    | ~ m1_subset_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_744,plain,(
    ~ m1_subset_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_742])).

tff(c_1569,plain,(
    ~ m1_subset_1(k7_relat_1('#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1567,c_744])).

tff(c_58006,plain,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_4','#skF_3')),'#skF_2')
    | ~ r1_tarski('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_57974,c_1569])).

tff(c_58080,plain,(
    ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_4','#skF_3')),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_58006])).

tff(c_58111,plain,
    ( ~ v5_relat_1(k7_relat_1('#skF_4','#skF_3'),'#skF_2')
    | ~ v1_relat_1(k7_relat_1('#skF_4','#skF_3')) ),
    inference(resolution,[status(thm)],[c_20,c_58080])).

tff(c_58119,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2258,c_2257,c_58111])).

tff(c_58121,plain,(
    m1_subset_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_742])).

tff(c_58626,plain,(
    k1_relset_1('#skF_3','#skF_2',k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')) = k1_relat_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')) ),
    inference(resolution,[status(thm)],[c_58121,c_58615])).

tff(c_59042,plain,(
    k1_relset_1('#skF_3','#skF_2',k7_relat_1('#skF_4','#skF_3')) = k1_relat_1(k7_relat_1('#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_59038,c_59038,c_58626])).

tff(c_58120,plain,(
    ~ v1_funct_2(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_742])).

tff(c_59049,plain,(
    ~ v1_funct_2(k7_relat_1('#skF_4','#skF_3'),'#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_59038,c_58120])).

tff(c_59048,plain,(
    m1_subset_1(k7_relat_1('#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_59038,c_58121])).

tff(c_52,plain,(
    ! [B_33,C_34,A_32] :
      ( k1_xboole_0 = B_33
      | v1_funct_2(C_34,A_32,B_33)
      | k1_relset_1(A_32,B_33,C_34) != A_32
      | ~ m1_subset_1(C_34,k1_zfmisc_1(k2_zfmisc_1(A_32,B_33))) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_59252,plain,
    ( k1_xboole_0 = '#skF_2'
    | v1_funct_2(k7_relat_1('#skF_4','#skF_3'),'#skF_3','#skF_2')
    | k1_relset_1('#skF_3','#skF_2',k7_relat_1('#skF_4','#skF_3')) != '#skF_3' ),
    inference(resolution,[status(thm)],[c_59048,c_52])).

tff(c_59279,plain,(
    k1_relset_1('#skF_3','#skF_2',k7_relat_1('#skF_4','#skF_3')) != '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_59049,c_93,c_59252])).

tff(c_59721,plain,(
    k1_relat_1(k7_relat_1('#skF_4','#skF_3')) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_59042,c_59279])).

tff(c_59806,plain,(
    ~ r1_tarski('#skF_3','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_59118,c_59721])).

tff(c_59810,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_59806])).

tff(c_59811,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_72])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_59815,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_59811,c_2])).

tff(c_59812,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_72])).

tff(c_59820,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_59811,c_59812])).

tff(c_59845,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_59820,c_76])).

tff(c_62489,plain,(
    ! [C_1873,A_1874,B_1875] :
      ( v1_xboole_0(C_1873)
      | ~ m1_subset_1(C_1873,k1_zfmisc_1(k2_zfmisc_1(A_1874,B_1875)))
      | ~ v1_xboole_0(A_1874) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_62495,plain,
    ( v1_xboole_0('#skF_4')
    | ~ v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_59845,c_62489])).

tff(c_62505,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_59815,c_62495])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_59834,plain,(
    ! [A_1] :
      ( A_1 = '#skF_1'
      | ~ v1_xboole_0(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_59811,c_4])).

tff(c_62514,plain,(
    '#skF_1' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_62505,c_59834])).

tff(c_59821,plain,(
    v1_funct_2('#skF_4','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_59820,c_78])).

tff(c_62545,plain,(
    v1_funct_2('#skF_4','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62514,c_62514,c_59821])).

tff(c_14,plain,(
    ! [A_6] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_6)) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_59841,plain,(
    ! [A_6] : m1_subset_1('#skF_1',k1_zfmisc_1(A_6)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_59811,c_14])).

tff(c_61971,plain,(
    ! [C_1827,B_1828,A_1829] :
      ( v5_relat_1(C_1827,B_1828)
      | ~ m1_subset_1(C_1827,k1_zfmisc_1(k2_zfmisc_1(A_1829,B_1828))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_61984,plain,(
    ! [B_1828] : v5_relat_1('#skF_1',B_1828) ),
    inference(resolution,[status(thm)],[c_59841,c_61971])).

tff(c_59857,plain,(
    ! [C_1610,A_1611,B_1612] :
      ( v1_relat_1(C_1610)
      | ~ m1_subset_1(C_1610,k1_zfmisc_1(k2_zfmisc_1(A_1611,B_1612))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_59866,plain,(
    v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_59841,c_59857])).

tff(c_24,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_59813,plain,(
    k2_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_59811,c_59811,c_24])).

tff(c_61828,plain,(
    ! [B_1815,A_1816] :
      ( r1_tarski(k2_relat_1(B_1815),A_1816)
      | ~ v5_relat_1(B_1815,A_1816)
      | ~ v1_relat_1(B_1815) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_61833,plain,(
    ! [A_1816] :
      ( r1_tarski('#skF_1',A_1816)
      | ~ v5_relat_1('#skF_1',A_1816)
      | ~ v1_relat_1('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_59813,c_61828])).

tff(c_61836,plain,(
    ! [A_1816] :
      ( r1_tarski('#skF_1',A_1816)
      | ~ v5_relat_1('#skF_1',A_1816) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_59866,c_61833])).

tff(c_61991,plain,(
    ! [A_1816] : r1_tarski('#skF_1',A_1816) ),
    inference(demodulation,[status(thm),theory(equality)],[c_61984,c_61836])).

tff(c_61787,plain,(
    ! [B_1807,A_1808] :
      ( B_1807 = A_1808
      | ~ r1_tarski(B_1807,A_1808)
      | ~ r1_tarski(A_1808,B_1807) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_61796,plain,
    ( '#skF_3' = '#skF_1'
    | ~ r1_tarski('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_74,c_61787])).

tff(c_61797,plain,(
    ~ r1_tarski('#skF_1','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_61796])).

tff(c_61996,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_61991,c_61797])).

tff(c_61997,plain,(
    '#skF_3' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_61796])).

tff(c_61008,plain,(
    ! [C_1736,A_1737,B_1738] :
      ( v1_xboole_0(C_1736)
      | ~ m1_subset_1(C_1736,k1_zfmisc_1(k2_zfmisc_1(A_1737,B_1738)))
      | ~ v1_xboole_0(A_1737) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_61011,plain,
    ( v1_xboole_0('#skF_4')
    | ~ v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_59845,c_61008])).

tff(c_61018,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_59815,c_61011])).

tff(c_61027,plain,(
    '#skF_1' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_61018,c_59834])).

tff(c_61045,plain,(
    ! [A_6] : m1_subset_1('#skF_4',k1_zfmisc_1(A_6)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_61027,c_59841])).

tff(c_22,plain,(
    ! [A_12] :
      ( k7_relat_1(A_12,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_59850,plain,(
    ! [A_12] :
      ( k7_relat_1(A_12,'#skF_1') = '#skF_1'
      | ~ v1_relat_1(A_12) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_59811,c_59811,c_22])).

tff(c_59875,plain,(
    k7_relat_1('#skF_1','#skF_1') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_59866,c_59850])).

tff(c_61038,plain,(
    k7_relat_1('#skF_4','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_61027,c_61027,c_61027,c_59875])).

tff(c_61770,plain,(
    ! [A_1803,B_1804,C_1805,D_1806] :
      ( k2_partfun1(A_1803,B_1804,C_1805,D_1806) = k7_relat_1(C_1805,D_1806)
      | ~ m1_subset_1(C_1805,k1_zfmisc_1(k2_zfmisc_1(A_1803,B_1804)))
      | ~ v1_funct_1(C_1805) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_61775,plain,(
    ! [A_1803,B_1804,D_1806] :
      ( k2_partfun1(A_1803,B_1804,'#skF_4',D_1806) = k7_relat_1('#skF_4',D_1806)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_61045,c_61770])).

tff(c_61779,plain,(
    ! [A_1803,B_1804,D_1806] : k2_partfun1(A_1803,B_1804,'#skF_4',D_1806) = k7_relat_1('#skF_4',D_1806) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_61775])).

tff(c_60829,plain,(
    ! [C_1712,B_1713,A_1714] :
      ( v5_relat_1(C_1712,B_1713)
      | ~ m1_subset_1(C_1712,k1_zfmisc_1(k2_zfmisc_1(A_1714,B_1713))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_60838,plain,(
    ! [B_1713] : v5_relat_1('#skF_1',B_1713) ),
    inference(resolution,[status(thm)],[c_59841,c_60829])).

tff(c_60744,plain,(
    ! [B_1699,A_1700] :
      ( r1_tarski(k2_relat_1(B_1699),A_1700)
      | ~ v5_relat_1(B_1699,A_1700)
      | ~ v1_relat_1(B_1699) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_60749,plain,(
    ! [A_1700] :
      ( r1_tarski('#skF_1',A_1700)
      | ~ v5_relat_1('#skF_1',A_1700)
      | ~ v1_relat_1('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_59813,c_60744])).

tff(c_60752,plain,(
    ! [A_1700] :
      ( r1_tarski('#skF_1',A_1700)
      | ~ v5_relat_1('#skF_1',A_1700) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_59866,c_60749])).

tff(c_60842,plain,(
    ! [A_1700] : r1_tarski('#skF_1',A_1700) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60838,c_60752])).

tff(c_60733,plain,(
    ! [B_1697,A_1698] :
      ( B_1697 = A_1698
      | ~ r1_tarski(B_1697,A_1698)
      | ~ r1_tarski(A_1698,B_1697) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_60742,plain,
    ( '#skF_3' = '#skF_1'
    | ~ r1_tarski('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_74,c_60733])).

tff(c_60743,plain,(
    ~ r1_tarski('#skF_1','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_60742])).

tff(c_60847,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_60842,c_60743])).

tff(c_60848,plain,(
    '#skF_3' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_60742])).

tff(c_60266,plain,(
    ! [C_1658,A_1659,B_1660] :
      ( v1_xboole_0(C_1658)
      | ~ m1_subset_1(C_1658,k1_zfmisc_1(k2_zfmisc_1(A_1659,B_1660)))
      | ~ v1_xboole_0(A_1659) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_60269,plain,
    ( v1_xboole_0('#skF_4')
    | ~ v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_59845,c_60266])).

tff(c_60276,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_59815,c_60269])).

tff(c_60285,plain,(
    '#skF_1' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_60276,c_59834])).

tff(c_60305,plain,(
    ! [A_6] : m1_subset_1('#skF_4',k1_zfmisc_1(A_6)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60285,c_59841])).

tff(c_60706,plain,(
    ! [A_1693,B_1694,C_1695,D_1696] :
      ( v1_funct_1(k2_partfun1(A_1693,B_1694,C_1695,D_1696))
      | ~ m1_subset_1(C_1695,k1_zfmisc_1(k2_zfmisc_1(A_1693,B_1694)))
      | ~ v1_funct_1(C_1695) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_60709,plain,(
    ! [A_1693,B_1694,D_1696] :
      ( v1_funct_1(k2_partfun1(A_1693,B_1694,'#skF_4',D_1696))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_60305,c_60706])).

tff(c_60712,plain,(
    ! [A_1693,B_1694,D_1696] : v1_funct_1(k2_partfun1(A_1693,B_1694,'#skF_4',D_1696)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_60709])).

tff(c_59917,plain,(
    ! [C_1617,B_1618,A_1619] :
      ( v5_relat_1(C_1617,B_1618)
      | ~ m1_subset_1(C_1617,k1_zfmisc_1(k2_zfmisc_1(A_1619,B_1618))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_59926,plain,(
    ! [B_1618] : v5_relat_1('#skF_1',B_1618) ),
    inference(resolution,[status(thm)],[c_59841,c_59917])).

tff(c_59956,plain,(
    ! [B_1628,A_1629] :
      ( r1_tarski(k2_relat_1(B_1628),A_1629)
      | ~ v5_relat_1(B_1628,A_1629)
      | ~ v1_relat_1(B_1628) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_59964,plain,(
    ! [A_1629] :
      ( r1_tarski('#skF_1',A_1629)
      | ~ v5_relat_1('#skF_1',A_1629)
      | ~ v1_relat_1('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_59813,c_59956])).

tff(c_59968,plain,(
    ! [A_1629] : r1_tarski('#skF_1',A_1629) ),
    inference(demodulation,[status(thm),theory(equality)],[c_59866,c_59926,c_59964])).

tff(c_59906,plain,(
    ! [B_1615,A_1616] :
      ( B_1615 = A_1616
      | ~ r1_tarski(B_1615,A_1616)
      | ~ r1_tarski(A_1616,B_1615) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_59915,plain,
    ( '#skF_3' = '#skF_1'
    | ~ r1_tarski('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_74,c_59906])).

tff(c_59916,plain,(
    ~ r1_tarski('#skF_1','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_59915])).

tff(c_59971,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_59968,c_59916])).

tff(c_59972,plain,(
    '#skF_3' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_59915])).

tff(c_59890,plain,
    ( ~ m1_subset_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1')))
    | ~ v1_funct_2(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_3'),'#skF_3','#skF_1')
    | ~ v1_funct_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_59820,c_59820,c_59820,c_59820,c_59820,c_70])).

tff(c_59891,plain,(
    ~ v1_funct_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_59890])).

tff(c_59984,plain,(
    ~ v1_funct_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_59972,c_59891])).

tff(c_60296,plain,(
    ~ v1_funct_1(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60285,c_60285,c_60285,c_59984])).

tff(c_60715,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_60712,c_60296])).

tff(c_60716,plain,
    ( ~ v1_funct_2(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_3'),'#skF_3','#skF_1')
    | ~ m1_subset_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_59890])).

tff(c_60732,plain,(
    ~ m1_subset_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_60716])).

tff(c_60887,plain,(
    ~ m1_subset_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60848,c_60848,c_60732])).

tff(c_61033,plain,(
    ~ m1_subset_1(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_61027,c_61027,c_61027,c_61027,c_61027,c_60887])).

tff(c_61781,plain,(
    ~ m1_subset_1(k7_relat_1('#skF_4','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_61779,c_61033])).

tff(c_61784,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_61045,c_61038,c_61781])).

tff(c_61786,plain,(
    m1_subset_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_60716])).

tff(c_62063,plain,(
    m1_subset_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_61997,c_61997,c_61786])).

tff(c_62492,plain,
    ( v1_xboole_0(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'))
    | ~ v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_62063,c_62489])).

tff(c_62502,plain,(
    v1_xboole_0(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_59815,c_62492])).

tff(c_62732,plain,(
    v1_xboole_0(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62514,c_62514,c_62514,c_62502])).

tff(c_12,plain,(
    ! [B_5,A_4] :
      ( ~ v1_xboole_0(B_5)
      | B_5 = A_4
      | ~ v1_xboole_0(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_62513,plain,(
    ! [A_4] :
      ( A_4 = '#skF_4'
      | ~ v1_xboole_0(A_4) ) ),
    inference(resolution,[status(thm)],[c_62505,c_12])).

tff(c_62738,plain,(
    k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_62732,c_62513])).

tff(c_61785,plain,(
    ~ v1_funct_2(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_3'),'#skF_3','#skF_1') ),
    inference(splitRight,[status(thm)],[c_60716])).

tff(c_62007,plain,(
    ~ v1_funct_2(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),'#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_61997,c_61997,c_61785])).

tff(c_62533,plain,(
    ~ v1_funct_2(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4'),'#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62514,c_62514,c_62514,c_62514,c_62514,c_62007])).

tff(c_62781,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_62545,c_62738,c_62533])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n014.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 16:42:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 20.86/11.45  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 20.90/11.48  
% 20.90/11.48  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 20.90/11.48  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_partfun1 > k1_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 20.90/11.48  
% 20.90/11.48  %Foreground sorts:
% 20.90/11.48  
% 20.90/11.48  
% 20.90/11.48  %Background operators:
% 20.90/11.48  
% 20.90/11.48  
% 20.90/11.48  %Foreground operators:
% 20.90/11.48  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 20.90/11.48  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 20.90/11.48  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 20.90/11.48  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 20.90/11.48  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 20.90/11.48  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 20.90/11.48  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 20.90/11.48  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 20.90/11.48  tff('#skF_2', type, '#skF_2': $i).
% 20.90/11.48  tff('#skF_3', type, '#skF_3': $i).
% 20.90/11.48  tff('#skF_1', type, '#skF_1': $i).
% 20.90/11.48  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 20.90/11.48  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 20.90/11.48  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 20.90/11.48  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 20.90/11.48  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 20.90/11.48  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 20.90/11.48  tff('#skF_4', type, '#skF_4': $i).
% 20.90/11.48  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 20.90/11.48  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 20.90/11.48  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 20.90/11.48  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 20.90/11.48  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 20.90/11.48  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 20.90/11.48  
% 20.90/11.50  tff(f_168, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_tarski(C, A) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | ((v1_funct_1(k2_partfun1(A, B, D, C)) & v1_funct_2(k2_partfun1(A, B, D, C), C, B)) & m1_subset_1(k2_partfun1(A, B, D, C), k1_zfmisc_1(k2_zfmisc_1(C, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_funct_2)).
% 20.90/11.50  tff(f_87, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 20.90/11.50  tff(f_104, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 20.90/11.50  tff(f_122, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 20.90/11.50  tff(f_71, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => (k1_relat_1(k7_relat_1(B, A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_relat_1)).
% 20.90/11.50  tff(f_136, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 20.90/11.50  tff(f_130, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (v1_funct_1(k2_partfun1(A, B, C, D)) & m1_subset_1(k2_partfun1(A, B, C, D), k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_partfun1)).
% 20.90/11.50  tff(f_93, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 20.90/11.50  tff(f_58, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 20.90/11.50  tff(f_148, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(k2_relat_1(B), A) => ((v1_funct_1(B) & v1_funct_2(B, k1_relat_1(B), A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B), A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_funct_2)).
% 20.90/11.50  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 20.90/11.50  tff(f_100, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_xboole_0(C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc3_relset_1)).
% 20.90/11.50  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 20.90/11.50  tff(f_46, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 20.90/11.50  tff(f_65, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 20.90/11.50  tff(f_36, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 20.90/11.50  tff(f_62, axiom, (![A]: (v1_relat_1(A) => (k7_relat_1(A, k1_xboole_0) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t110_relat_1)).
% 20.90/11.50  tff(f_44, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_boole)).
% 20.90/11.50  tff(c_74, plain, (r1_tarski('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_168])).
% 20.90/11.50  tff(c_76, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_168])).
% 20.90/11.50  tff(c_58122, plain, (![C_1468, A_1469, B_1470]: (v1_relat_1(C_1468) | ~m1_subset_1(C_1468, k1_zfmisc_1(k2_zfmisc_1(A_1469, B_1470))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 20.90/11.50  tff(c_58131, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_76, c_58122])).
% 20.90/11.50  tff(c_72, plain, (k1_xboole_0='#skF_1' | k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_168])).
% 20.90/11.50  tff(c_93, plain, (k1_xboole_0!='#skF_2'), inference(splitLeft, [status(thm)], [c_72])).
% 20.90/11.50  tff(c_78, plain, (v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_168])).
% 20.90/11.50  tff(c_58615, plain, (![A_1513, B_1514, C_1515]: (k1_relset_1(A_1513, B_1514, C_1515)=k1_relat_1(C_1515) | ~m1_subset_1(C_1515, k1_zfmisc_1(k2_zfmisc_1(A_1513, B_1514))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 20.90/11.50  tff(c_58629, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_76, c_58615])).
% 20.90/11.50  tff(c_59067, plain, (![B_1560, A_1561, C_1562]: (k1_xboole_0=B_1560 | k1_relset_1(A_1561, B_1560, C_1562)=A_1561 | ~v1_funct_2(C_1562, A_1561, B_1560) | ~m1_subset_1(C_1562, k1_zfmisc_1(k2_zfmisc_1(A_1561, B_1560))))), inference(cnfTransformation, [status(thm)], [f_122])).
% 20.90/11.50  tff(c_59077, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_1' | ~v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_76, c_59067])).
% 20.90/11.50  tff(c_59083, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_78, c_58629, c_59077])).
% 20.90/11.50  tff(c_59084, plain, (k1_relat_1('#skF_4')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_93, c_59083])).
% 20.90/11.50  tff(c_28, plain, (![B_14, A_13]: (k1_relat_1(k7_relat_1(B_14, A_13))=A_13 | ~r1_tarski(A_13, k1_relat_1(B_14)) | ~v1_relat_1(B_14))), inference(cnfTransformation, [status(thm)], [f_71])).
% 20.90/11.50  tff(c_59104, plain, (![A_13]: (k1_relat_1(k7_relat_1('#skF_4', A_13))=A_13 | ~r1_tarski(A_13, '#skF_1') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_59084, c_28])).
% 20.90/11.50  tff(c_59118, plain, (![A_13]: (k1_relat_1(k7_relat_1('#skF_4', A_13))=A_13 | ~r1_tarski(A_13, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_58131, c_59104])).
% 20.90/11.50  tff(c_80, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_168])).
% 20.90/11.50  tff(c_59019, plain, (![A_1554, B_1555, C_1556, D_1557]: (k2_partfun1(A_1554, B_1555, C_1556, D_1557)=k7_relat_1(C_1556, D_1557) | ~m1_subset_1(C_1556, k1_zfmisc_1(k2_zfmisc_1(A_1554, B_1555))) | ~v1_funct_1(C_1556))), inference(cnfTransformation, [status(thm)], [f_136])).
% 20.90/11.50  tff(c_59028, plain, (![D_1557]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_1557)=k7_relat_1('#skF_4', D_1557) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_76, c_59019])).
% 20.90/11.50  tff(c_59038, plain, (![D_1557]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_1557)=k7_relat_1('#skF_4', D_1557))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_59028])).
% 20.90/11.50  tff(c_1553, plain, (![A_206, B_207, C_208, D_209]: (k2_partfun1(A_206, B_207, C_208, D_209)=k7_relat_1(C_208, D_209) | ~m1_subset_1(C_208, k1_zfmisc_1(k2_zfmisc_1(A_206, B_207))) | ~v1_funct_1(C_208))), inference(cnfTransformation, [status(thm)], [f_136])).
% 20.90/11.50  tff(c_1560, plain, (![D_209]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_209)=k7_relat_1('#skF_4', D_209) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_76, c_1553])).
% 20.90/11.50  tff(c_1567, plain, (![D_209]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_209)=k7_relat_1('#skF_4', D_209))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_1560])).
% 20.90/11.50  tff(c_2148, plain, (![A_240, B_241, C_242, D_243]: (m1_subset_1(k2_partfun1(A_240, B_241, C_242, D_243), k1_zfmisc_1(k2_zfmisc_1(A_240, B_241))) | ~m1_subset_1(C_242, k1_zfmisc_1(k2_zfmisc_1(A_240, B_241))) | ~v1_funct_1(C_242))), inference(cnfTransformation, [status(thm)], [f_130])).
% 20.90/11.50  tff(c_2193, plain, (![D_209]: (m1_subset_1(k7_relat_1('#skF_4', D_209), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1567, c_2148])).
% 20.90/11.51  tff(c_2211, plain, (![D_244]: (m1_subset_1(k7_relat_1('#skF_4', D_244), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_76, c_2193])).
% 20.90/11.51  tff(c_36, plain, (![C_21, A_19, B_20]: (v1_relat_1(C_21) | ~m1_subset_1(C_21, k1_zfmisc_1(k2_zfmisc_1(A_19, B_20))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 20.90/11.51  tff(c_2258, plain, (![D_244]: (v1_relat_1(k7_relat_1('#skF_4', D_244)))), inference(resolution, [status(thm)], [c_2211, c_36])).
% 20.90/11.51  tff(c_38, plain, (![C_24, B_23, A_22]: (v5_relat_1(C_24, B_23) | ~m1_subset_1(C_24, k1_zfmisc_1(k2_zfmisc_1(A_22, B_23))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 20.90/11.51  tff(c_2257, plain, (![D_244]: (v5_relat_1(k7_relat_1('#skF_4', D_244), '#skF_2'))), inference(resolution, [status(thm)], [c_2211, c_38])).
% 20.90/11.51  tff(c_20, plain, (![B_11, A_10]: (r1_tarski(k2_relat_1(B_11), A_10) | ~v5_relat_1(B_11, A_10) | ~v1_relat_1(B_11))), inference(cnfTransformation, [status(thm)], [f_58])).
% 20.90/11.51  tff(c_1244, plain, (![A_177, B_178, C_179, D_180]: (v1_funct_1(k2_partfun1(A_177, B_178, C_179, D_180)) | ~m1_subset_1(C_179, k1_zfmisc_1(k2_zfmisc_1(A_177, B_178))) | ~v1_funct_1(C_179))), inference(cnfTransformation, [status(thm)], [f_130])).
% 20.90/11.51  tff(c_1249, plain, (![D_180]: (v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_180)) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_76, c_1244])).
% 20.90/11.51  tff(c_1255, plain, (![D_180]: (v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_180)))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_1249])).
% 20.90/11.51  tff(c_1568, plain, (![D_180]: (v1_funct_1(k7_relat_1('#skF_4', D_180)))), inference(demodulation, [status(thm), theory('equality')], [c_1567, c_1255])).
% 20.90/11.51  tff(c_745, plain, (![C_122, A_123, B_124]: (v1_relat_1(C_122) | ~m1_subset_1(C_122, k1_zfmisc_1(k2_zfmisc_1(A_123, B_124))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 20.90/11.51  tff(c_754, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_76, c_745])).
% 20.90/11.51  tff(c_1053, plain, (![A_162, B_163, C_164]: (k1_relset_1(A_162, B_163, C_164)=k1_relat_1(C_164) | ~m1_subset_1(C_164, k1_zfmisc_1(k2_zfmisc_1(A_162, B_163))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 20.90/11.51  tff(c_1063, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_76, c_1053])).
% 20.90/11.51  tff(c_1714, plain, (![B_225, A_226, C_227]: (k1_xboole_0=B_225 | k1_relset_1(A_226, B_225, C_227)=A_226 | ~v1_funct_2(C_227, A_226, B_225) | ~m1_subset_1(C_227, k1_zfmisc_1(k2_zfmisc_1(A_226, B_225))))), inference(cnfTransformation, [status(thm)], [f_122])).
% 20.90/11.51  tff(c_1724, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_1' | ~v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_76, c_1714])).
% 20.90/11.51  tff(c_1730, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_78, c_1063, c_1724])).
% 20.90/11.51  tff(c_1731, plain, (k1_relat_1('#skF_4')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_93, c_1730])).
% 20.90/11.51  tff(c_1751, plain, (![A_13]: (k1_relat_1(k7_relat_1('#skF_4', A_13))=A_13 | ~r1_tarski(A_13, '#skF_1') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1731, c_28])).
% 20.90/11.51  tff(c_1838, plain, (![A_232]: (k1_relat_1(k7_relat_1('#skF_4', A_232))=A_232 | ~r1_tarski(A_232, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_754, c_1751])).
% 20.90/11.51  tff(c_64, plain, (![B_44, A_43]: (m1_subset_1(B_44, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_44), A_43))) | ~r1_tarski(k2_relat_1(B_44), A_43) | ~v1_funct_1(B_44) | ~v1_relat_1(B_44))), inference(cnfTransformation, [status(thm)], [f_148])).
% 20.90/11.51  tff(c_1857, plain, (![A_232, A_43]: (m1_subset_1(k7_relat_1('#skF_4', A_232), k1_zfmisc_1(k2_zfmisc_1(A_232, A_43))) | ~r1_tarski(k2_relat_1(k7_relat_1('#skF_4', A_232)), A_43) | ~v1_funct_1(k7_relat_1('#skF_4', A_232)) | ~v1_relat_1(k7_relat_1('#skF_4', A_232)) | ~r1_tarski(A_232, '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_1838, c_64])).
% 20.90/11.51  tff(c_1908, plain, (![A_232, A_43]: (m1_subset_1(k7_relat_1('#skF_4', A_232), k1_zfmisc_1(k2_zfmisc_1(A_232, A_43))) | ~r1_tarski(k2_relat_1(k7_relat_1('#skF_4', A_232)), A_43) | ~v1_relat_1(k7_relat_1('#skF_4', A_232)) | ~r1_tarski(A_232, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_1568, c_1857])).
% 20.90/11.51  tff(c_57974, plain, (![A_1466, A_1467]: (m1_subset_1(k7_relat_1('#skF_4', A_1466), k1_zfmisc_1(k2_zfmisc_1(A_1466, A_1467))) | ~r1_tarski(k2_relat_1(k7_relat_1('#skF_4', A_1466)), A_1467) | ~r1_tarski(A_1466, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_2258, c_1908])).
% 20.90/11.51  tff(c_727, plain, (![A_118, B_119, C_120, D_121]: (v1_funct_1(k2_partfun1(A_118, B_119, C_120, D_121)) | ~m1_subset_1(C_120, k1_zfmisc_1(k2_zfmisc_1(A_118, B_119))) | ~v1_funct_1(C_120))), inference(cnfTransformation, [status(thm)], [f_130])).
% 20.90/11.51  tff(c_732, plain, (![D_121]: (v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_121)) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_76, c_727])).
% 20.90/11.51  tff(c_738, plain, (![D_121]: (v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_121)))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_732])).
% 20.90/11.51  tff(c_70, plain, (~m1_subset_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_2(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_3', '#skF_2') | ~v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_168])).
% 20.90/11.51  tff(c_124, plain, (~v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))), inference(splitLeft, [status(thm)], [c_70])).
% 20.90/11.51  tff(c_741, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_738, c_124])).
% 20.90/11.51  tff(c_742, plain, (~v1_funct_2(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_3', '#skF_2') | ~m1_subset_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitRight, [status(thm)], [c_70])).
% 20.90/11.51  tff(c_744, plain, (~m1_subset_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitLeft, [status(thm)], [c_742])).
% 20.90/11.51  tff(c_1569, plain, (~m1_subset_1(k7_relat_1('#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_1567, c_744])).
% 20.90/11.51  tff(c_58006, plain, (~r1_tarski(k2_relat_1(k7_relat_1('#skF_4', '#skF_3')), '#skF_2') | ~r1_tarski('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_57974, c_1569])).
% 20.90/11.51  tff(c_58080, plain, (~r1_tarski(k2_relat_1(k7_relat_1('#skF_4', '#skF_3')), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_58006])).
% 20.90/11.51  tff(c_58111, plain, (~v5_relat_1(k7_relat_1('#skF_4', '#skF_3'), '#skF_2') | ~v1_relat_1(k7_relat_1('#skF_4', '#skF_3'))), inference(resolution, [status(thm)], [c_20, c_58080])).
% 20.90/11.51  tff(c_58119, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2258, c_2257, c_58111])).
% 20.90/11.51  tff(c_58121, plain, (m1_subset_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitRight, [status(thm)], [c_742])).
% 20.90/11.51  tff(c_58626, plain, (k1_relset_1('#skF_3', '#skF_2', k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))=k1_relat_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))), inference(resolution, [status(thm)], [c_58121, c_58615])).
% 20.90/11.51  tff(c_59042, plain, (k1_relset_1('#skF_3', '#skF_2', k7_relat_1('#skF_4', '#skF_3'))=k1_relat_1(k7_relat_1('#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_59038, c_59038, c_58626])).
% 20.90/11.51  tff(c_58120, plain, (~v1_funct_2(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_742])).
% 20.90/11.51  tff(c_59049, plain, (~v1_funct_2(k7_relat_1('#skF_4', '#skF_3'), '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_59038, c_58120])).
% 20.90/11.51  tff(c_59048, plain, (m1_subset_1(k7_relat_1('#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_59038, c_58121])).
% 20.90/11.51  tff(c_52, plain, (![B_33, C_34, A_32]: (k1_xboole_0=B_33 | v1_funct_2(C_34, A_32, B_33) | k1_relset_1(A_32, B_33, C_34)!=A_32 | ~m1_subset_1(C_34, k1_zfmisc_1(k2_zfmisc_1(A_32, B_33))))), inference(cnfTransformation, [status(thm)], [f_122])).
% 20.90/11.51  tff(c_59252, plain, (k1_xboole_0='#skF_2' | v1_funct_2(k7_relat_1('#skF_4', '#skF_3'), '#skF_3', '#skF_2') | k1_relset_1('#skF_3', '#skF_2', k7_relat_1('#skF_4', '#skF_3'))!='#skF_3'), inference(resolution, [status(thm)], [c_59048, c_52])).
% 20.90/11.51  tff(c_59279, plain, (k1_relset_1('#skF_3', '#skF_2', k7_relat_1('#skF_4', '#skF_3'))!='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_59049, c_93, c_59252])).
% 20.90/11.51  tff(c_59721, plain, (k1_relat_1(k7_relat_1('#skF_4', '#skF_3'))!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_59042, c_59279])).
% 20.90/11.51  tff(c_59806, plain, (~r1_tarski('#skF_3', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_59118, c_59721])).
% 20.90/11.51  tff(c_59810, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_74, c_59806])).
% 20.90/11.51  tff(c_59811, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_72])).
% 20.90/11.51  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 20.90/11.51  tff(c_59815, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_59811, c_2])).
% 20.90/11.51  tff(c_59812, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_72])).
% 20.90/11.51  tff(c_59820, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_59811, c_59812])).
% 20.90/11.51  tff(c_59845, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_59820, c_76])).
% 20.90/11.51  tff(c_62489, plain, (![C_1873, A_1874, B_1875]: (v1_xboole_0(C_1873) | ~m1_subset_1(C_1873, k1_zfmisc_1(k2_zfmisc_1(A_1874, B_1875))) | ~v1_xboole_0(A_1874))), inference(cnfTransformation, [status(thm)], [f_100])).
% 20.90/11.51  tff(c_62495, plain, (v1_xboole_0('#skF_4') | ~v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_59845, c_62489])).
% 20.90/11.51  tff(c_62505, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_59815, c_62495])).
% 20.90/11.51  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 20.90/11.51  tff(c_59834, plain, (![A_1]: (A_1='#skF_1' | ~v1_xboole_0(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_59811, c_4])).
% 20.90/11.51  tff(c_62514, plain, ('#skF_1'='#skF_4'), inference(resolution, [status(thm)], [c_62505, c_59834])).
% 20.90/11.51  tff(c_59821, plain, (v1_funct_2('#skF_4', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_59820, c_78])).
% 20.90/11.51  tff(c_62545, plain, (v1_funct_2('#skF_4', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_62514, c_62514, c_59821])).
% 20.90/11.51  tff(c_14, plain, (![A_6]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 20.90/11.51  tff(c_59841, plain, (![A_6]: (m1_subset_1('#skF_1', k1_zfmisc_1(A_6)))), inference(demodulation, [status(thm), theory('equality')], [c_59811, c_14])).
% 20.90/11.51  tff(c_61971, plain, (![C_1827, B_1828, A_1829]: (v5_relat_1(C_1827, B_1828) | ~m1_subset_1(C_1827, k1_zfmisc_1(k2_zfmisc_1(A_1829, B_1828))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 20.90/11.51  tff(c_61984, plain, (![B_1828]: (v5_relat_1('#skF_1', B_1828))), inference(resolution, [status(thm)], [c_59841, c_61971])).
% 20.90/11.51  tff(c_59857, plain, (![C_1610, A_1611, B_1612]: (v1_relat_1(C_1610) | ~m1_subset_1(C_1610, k1_zfmisc_1(k2_zfmisc_1(A_1611, B_1612))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 20.90/11.51  tff(c_59866, plain, (v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_59841, c_59857])).
% 20.90/11.51  tff(c_24, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_65])).
% 20.90/11.51  tff(c_59813, plain, (k2_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_59811, c_59811, c_24])).
% 20.90/11.51  tff(c_61828, plain, (![B_1815, A_1816]: (r1_tarski(k2_relat_1(B_1815), A_1816) | ~v5_relat_1(B_1815, A_1816) | ~v1_relat_1(B_1815))), inference(cnfTransformation, [status(thm)], [f_58])).
% 20.90/11.51  tff(c_61833, plain, (![A_1816]: (r1_tarski('#skF_1', A_1816) | ~v5_relat_1('#skF_1', A_1816) | ~v1_relat_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_59813, c_61828])).
% 20.90/11.51  tff(c_61836, plain, (![A_1816]: (r1_tarski('#skF_1', A_1816) | ~v5_relat_1('#skF_1', A_1816))), inference(demodulation, [status(thm), theory('equality')], [c_59866, c_61833])).
% 20.90/11.51  tff(c_61991, plain, (![A_1816]: (r1_tarski('#skF_1', A_1816))), inference(demodulation, [status(thm), theory('equality')], [c_61984, c_61836])).
% 20.90/11.51  tff(c_61787, plain, (![B_1807, A_1808]: (B_1807=A_1808 | ~r1_tarski(B_1807, A_1808) | ~r1_tarski(A_1808, B_1807))), inference(cnfTransformation, [status(thm)], [f_36])).
% 20.90/11.51  tff(c_61796, plain, ('#skF_3'='#skF_1' | ~r1_tarski('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_74, c_61787])).
% 20.90/11.51  tff(c_61797, plain, (~r1_tarski('#skF_1', '#skF_3')), inference(splitLeft, [status(thm)], [c_61796])).
% 20.90/11.51  tff(c_61996, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_61991, c_61797])).
% 20.90/11.51  tff(c_61997, plain, ('#skF_3'='#skF_1'), inference(splitRight, [status(thm)], [c_61796])).
% 20.90/11.51  tff(c_61008, plain, (![C_1736, A_1737, B_1738]: (v1_xboole_0(C_1736) | ~m1_subset_1(C_1736, k1_zfmisc_1(k2_zfmisc_1(A_1737, B_1738))) | ~v1_xboole_0(A_1737))), inference(cnfTransformation, [status(thm)], [f_100])).
% 20.90/11.51  tff(c_61011, plain, (v1_xboole_0('#skF_4') | ~v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_59845, c_61008])).
% 20.90/11.51  tff(c_61018, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_59815, c_61011])).
% 20.90/11.51  tff(c_61027, plain, ('#skF_1'='#skF_4'), inference(resolution, [status(thm)], [c_61018, c_59834])).
% 20.90/11.51  tff(c_61045, plain, (![A_6]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_6)))), inference(demodulation, [status(thm), theory('equality')], [c_61027, c_59841])).
% 20.90/11.51  tff(c_22, plain, (![A_12]: (k7_relat_1(A_12, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_62])).
% 20.90/11.51  tff(c_59850, plain, (![A_12]: (k7_relat_1(A_12, '#skF_1')='#skF_1' | ~v1_relat_1(A_12))), inference(demodulation, [status(thm), theory('equality')], [c_59811, c_59811, c_22])).
% 20.90/11.51  tff(c_59875, plain, (k7_relat_1('#skF_1', '#skF_1')='#skF_1'), inference(resolution, [status(thm)], [c_59866, c_59850])).
% 20.90/11.51  tff(c_61038, plain, (k7_relat_1('#skF_4', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_61027, c_61027, c_61027, c_59875])).
% 20.90/11.51  tff(c_61770, plain, (![A_1803, B_1804, C_1805, D_1806]: (k2_partfun1(A_1803, B_1804, C_1805, D_1806)=k7_relat_1(C_1805, D_1806) | ~m1_subset_1(C_1805, k1_zfmisc_1(k2_zfmisc_1(A_1803, B_1804))) | ~v1_funct_1(C_1805))), inference(cnfTransformation, [status(thm)], [f_136])).
% 20.90/11.51  tff(c_61775, plain, (![A_1803, B_1804, D_1806]: (k2_partfun1(A_1803, B_1804, '#skF_4', D_1806)=k7_relat_1('#skF_4', D_1806) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_61045, c_61770])).
% 20.90/11.51  tff(c_61779, plain, (![A_1803, B_1804, D_1806]: (k2_partfun1(A_1803, B_1804, '#skF_4', D_1806)=k7_relat_1('#skF_4', D_1806))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_61775])).
% 20.90/11.51  tff(c_60829, plain, (![C_1712, B_1713, A_1714]: (v5_relat_1(C_1712, B_1713) | ~m1_subset_1(C_1712, k1_zfmisc_1(k2_zfmisc_1(A_1714, B_1713))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 20.90/11.51  tff(c_60838, plain, (![B_1713]: (v5_relat_1('#skF_1', B_1713))), inference(resolution, [status(thm)], [c_59841, c_60829])).
% 20.90/11.51  tff(c_60744, plain, (![B_1699, A_1700]: (r1_tarski(k2_relat_1(B_1699), A_1700) | ~v5_relat_1(B_1699, A_1700) | ~v1_relat_1(B_1699))), inference(cnfTransformation, [status(thm)], [f_58])).
% 20.90/11.51  tff(c_60749, plain, (![A_1700]: (r1_tarski('#skF_1', A_1700) | ~v5_relat_1('#skF_1', A_1700) | ~v1_relat_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_59813, c_60744])).
% 20.90/11.51  tff(c_60752, plain, (![A_1700]: (r1_tarski('#skF_1', A_1700) | ~v5_relat_1('#skF_1', A_1700))), inference(demodulation, [status(thm), theory('equality')], [c_59866, c_60749])).
% 20.90/11.51  tff(c_60842, plain, (![A_1700]: (r1_tarski('#skF_1', A_1700))), inference(demodulation, [status(thm), theory('equality')], [c_60838, c_60752])).
% 20.90/11.51  tff(c_60733, plain, (![B_1697, A_1698]: (B_1697=A_1698 | ~r1_tarski(B_1697, A_1698) | ~r1_tarski(A_1698, B_1697))), inference(cnfTransformation, [status(thm)], [f_36])).
% 20.90/11.51  tff(c_60742, plain, ('#skF_3'='#skF_1' | ~r1_tarski('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_74, c_60733])).
% 20.90/11.51  tff(c_60743, plain, (~r1_tarski('#skF_1', '#skF_3')), inference(splitLeft, [status(thm)], [c_60742])).
% 20.90/11.51  tff(c_60847, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_60842, c_60743])).
% 20.90/11.51  tff(c_60848, plain, ('#skF_3'='#skF_1'), inference(splitRight, [status(thm)], [c_60742])).
% 20.90/11.51  tff(c_60266, plain, (![C_1658, A_1659, B_1660]: (v1_xboole_0(C_1658) | ~m1_subset_1(C_1658, k1_zfmisc_1(k2_zfmisc_1(A_1659, B_1660))) | ~v1_xboole_0(A_1659))), inference(cnfTransformation, [status(thm)], [f_100])).
% 20.90/11.51  tff(c_60269, plain, (v1_xboole_0('#skF_4') | ~v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_59845, c_60266])).
% 20.90/11.51  tff(c_60276, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_59815, c_60269])).
% 20.90/11.51  tff(c_60285, plain, ('#skF_1'='#skF_4'), inference(resolution, [status(thm)], [c_60276, c_59834])).
% 20.90/11.51  tff(c_60305, plain, (![A_6]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_6)))), inference(demodulation, [status(thm), theory('equality')], [c_60285, c_59841])).
% 20.90/11.51  tff(c_60706, plain, (![A_1693, B_1694, C_1695, D_1696]: (v1_funct_1(k2_partfun1(A_1693, B_1694, C_1695, D_1696)) | ~m1_subset_1(C_1695, k1_zfmisc_1(k2_zfmisc_1(A_1693, B_1694))) | ~v1_funct_1(C_1695))), inference(cnfTransformation, [status(thm)], [f_130])).
% 20.90/11.51  tff(c_60709, plain, (![A_1693, B_1694, D_1696]: (v1_funct_1(k2_partfun1(A_1693, B_1694, '#skF_4', D_1696)) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_60305, c_60706])).
% 20.90/11.51  tff(c_60712, plain, (![A_1693, B_1694, D_1696]: (v1_funct_1(k2_partfun1(A_1693, B_1694, '#skF_4', D_1696)))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_60709])).
% 20.90/11.51  tff(c_59917, plain, (![C_1617, B_1618, A_1619]: (v5_relat_1(C_1617, B_1618) | ~m1_subset_1(C_1617, k1_zfmisc_1(k2_zfmisc_1(A_1619, B_1618))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 20.90/11.51  tff(c_59926, plain, (![B_1618]: (v5_relat_1('#skF_1', B_1618))), inference(resolution, [status(thm)], [c_59841, c_59917])).
% 20.90/11.51  tff(c_59956, plain, (![B_1628, A_1629]: (r1_tarski(k2_relat_1(B_1628), A_1629) | ~v5_relat_1(B_1628, A_1629) | ~v1_relat_1(B_1628))), inference(cnfTransformation, [status(thm)], [f_58])).
% 20.90/11.51  tff(c_59964, plain, (![A_1629]: (r1_tarski('#skF_1', A_1629) | ~v5_relat_1('#skF_1', A_1629) | ~v1_relat_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_59813, c_59956])).
% 20.90/11.51  tff(c_59968, plain, (![A_1629]: (r1_tarski('#skF_1', A_1629))), inference(demodulation, [status(thm), theory('equality')], [c_59866, c_59926, c_59964])).
% 20.90/11.51  tff(c_59906, plain, (![B_1615, A_1616]: (B_1615=A_1616 | ~r1_tarski(B_1615, A_1616) | ~r1_tarski(A_1616, B_1615))), inference(cnfTransformation, [status(thm)], [f_36])).
% 20.90/11.51  tff(c_59915, plain, ('#skF_3'='#skF_1' | ~r1_tarski('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_74, c_59906])).
% 20.90/11.51  tff(c_59916, plain, (~r1_tarski('#skF_1', '#skF_3')), inference(splitLeft, [status(thm)], [c_59915])).
% 20.90/11.51  tff(c_59971, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_59968, c_59916])).
% 20.90/11.51  tff(c_59972, plain, ('#skF_3'='#skF_1'), inference(splitRight, [status(thm)], [c_59915])).
% 20.90/11.51  tff(c_59890, plain, (~m1_subset_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1'))) | ~v1_funct_2(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_3'), '#skF_3', '#skF_1') | ~v1_funct_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_59820, c_59820, c_59820, c_59820, c_59820, c_70])).
% 20.90/11.51  tff(c_59891, plain, (~v1_funct_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_3'))), inference(splitLeft, [status(thm)], [c_59890])).
% 20.90/11.51  tff(c_59984, plain, (~v1_funct_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_59972, c_59891])).
% 20.90/11.51  tff(c_60296, plain, (~v1_funct_1(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_60285, c_60285, c_60285, c_59984])).
% 20.90/11.51  tff(c_60715, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_60712, c_60296])).
% 20.90/11.51  tff(c_60716, plain, (~v1_funct_2(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_3'), '#skF_3', '#skF_1') | ~m1_subset_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1')))), inference(splitRight, [status(thm)], [c_59890])).
% 20.90/11.51  tff(c_60732, plain, (~m1_subset_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1')))), inference(splitLeft, [status(thm)], [c_60716])).
% 20.90/11.51  tff(c_60887, plain, (~m1_subset_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_60848, c_60848, c_60732])).
% 20.90/11.51  tff(c_61033, plain, (~m1_subset_1(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_61027, c_61027, c_61027, c_61027, c_61027, c_60887])).
% 20.90/11.51  tff(c_61781, plain, (~m1_subset_1(k7_relat_1('#skF_4', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_61779, c_61033])).
% 20.90/11.51  tff(c_61784, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_61045, c_61038, c_61781])).
% 20.90/11.51  tff(c_61786, plain, (m1_subset_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1')))), inference(splitRight, [status(thm)], [c_60716])).
% 20.90/11.51  tff(c_62063, plain, (m1_subset_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_61997, c_61997, c_61786])).
% 20.90/11.51  tff(c_62492, plain, (v1_xboole_0(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1')) | ~v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_62063, c_62489])).
% 20.90/11.51  tff(c_62502, plain, (v1_xboole_0(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_59815, c_62492])).
% 20.90/11.51  tff(c_62732, plain, (v1_xboole_0(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_62514, c_62514, c_62514, c_62502])).
% 20.90/11.51  tff(c_12, plain, (![B_5, A_4]: (~v1_xboole_0(B_5) | B_5=A_4 | ~v1_xboole_0(A_4))), inference(cnfTransformation, [status(thm)], [f_44])).
% 20.90/11.51  tff(c_62513, plain, (![A_4]: (A_4='#skF_4' | ~v1_xboole_0(A_4))), inference(resolution, [status(thm)], [c_62505, c_12])).
% 20.90/11.51  tff(c_62738, plain, (k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_62732, c_62513])).
% 20.90/11.51  tff(c_61785, plain, (~v1_funct_2(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_3'), '#skF_3', '#skF_1')), inference(splitRight, [status(thm)], [c_60716])).
% 20.90/11.51  tff(c_62007, plain, (~v1_funct_2(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_61997, c_61997, c_61785])).
% 20.90/11.51  tff(c_62533, plain, (~v1_funct_2(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'), '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_62514, c_62514, c_62514, c_62514, c_62514, c_62007])).
% 20.90/11.51  tff(c_62781, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_62545, c_62738, c_62533])).
% 20.90/11.51  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 20.90/11.51  
% 20.90/11.51  Inference rules
% 20.90/11.51  ----------------------
% 20.90/11.51  #Ref     : 0
% 20.90/11.51  #Sup     : 13044
% 20.90/11.51  #Fact    : 0
% 20.90/11.51  #Define  : 0
% 20.90/11.51  #Split   : 37
% 20.90/11.51  #Chain   : 0
% 20.90/11.51  #Close   : 0
% 20.90/11.51  
% 20.90/11.51  Ordering : KBO
% 20.90/11.51  
% 20.90/11.51  Simplification rules
% 20.90/11.51  ----------------------
% 20.90/11.51  #Subsume      : 3936
% 20.90/11.51  #Demod        : 26259
% 20.90/11.51  #Tautology    : 4780
% 20.90/11.51  #SimpNegUnit  : 239
% 20.90/11.51  #BackRed      : 258
% 20.90/11.51  
% 20.90/11.51  #Partial instantiations: 0
% 20.90/11.51  #Strategies tried      : 1
% 20.90/11.51  
% 20.90/11.51  Timing (in seconds)
% 20.90/11.51  ----------------------
% 20.90/11.51  Preprocessing        : 0.36
% 20.90/11.51  Parsing              : 0.19
% 20.90/11.51  CNF conversion       : 0.02
% 20.90/11.51  Main loop            : 10.35
% 20.90/11.51  Inferencing          : 1.94
% 20.90/11.51  Reduction            : 4.70
% 20.90/11.51  Demodulation         : 3.90
% 20.90/11.51  BG Simplification    : 0.17
% 20.90/11.51  Subsumption          : 3.05
% 21.13/11.51  Abstraction          : 0.34
% 21.13/11.51  MUC search           : 0.00
% 21.13/11.51  Cooper               : 0.00
% 21.13/11.51  Total                : 10.77
% 21.13/11.51  Index Insertion      : 0.00
% 21.13/11.51  Index Deletion       : 0.00
% 21.13/11.51  Index Matching       : 0.00
% 21.13/11.51  BG Taut test         : 0.00
%------------------------------------------------------------------------------
