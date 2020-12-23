%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:18 EST 2020

% Result     : Theorem 4.14s
% Output     : CNFRefutation 4.14s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 309 expanded)
%              Number of leaves         :   39 ( 122 expanded)
%              Depth                    :   12
%              Number of atoms          :  175 ( 874 expanded)
%              Number of equality atoms :   56 ( 200 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_4 > #skF_8 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_157,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [D] :
            ( ( v1_funct_1(D)
              & v1_funct_2(D,A,B)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
           => ( ! [E] :
                  ( m1_subset_1(E,A)
                 => k1_funct_1(C,E) = k1_funct_1(D,E) )
             => r2_relset_1(A,B,C,D) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_funct_2)).

tff(f_93,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_relset_1)).

tff(f_105,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_86,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_97,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_136,axiom,(
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

tff(f_77,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( ( k1_relat_1(A) = k1_relat_1(B)
              & ! [C] :
                  ( r2_hidden(C,k1_relat_1(A))
                 => k1_funct_1(A,C) = k1_funct_1(B,C) ) )
           => A = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_funct_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_82,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_41,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).

tff(f_49,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(c_60,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_656,plain,(
    ! [C_122,B_123,A_124] :
      ( v1_xboole_0(C_122)
      | ~ m1_subset_1(C_122,k1_zfmisc_1(k2_zfmisc_1(B_123,A_124)))
      | ~ v1_xboole_0(A_124) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_678,plain,
    ( v1_xboole_0('#skF_8')
    | ~ v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_60,c_656])).

tff(c_685,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_678])).

tff(c_722,plain,(
    ! [A_133,B_134,D_135] :
      ( r2_relset_1(A_133,B_134,D_135,D_135)
      | ~ m1_subset_1(D_135,k1_zfmisc_1(k2_zfmisc_1(A_133,B_134))) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_738,plain,(
    r2_relset_1('#skF_5','#skF_6','#skF_8','#skF_8') ),
    inference(resolution,[status(thm)],[c_60,c_722])).

tff(c_66,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_140,plain,(
    ! [C_70,A_71,B_72] :
      ( v1_relat_1(C_70)
      | ~ m1_subset_1(C_70,k1_zfmisc_1(k2_zfmisc_1(A_71,B_72))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_161,plain,(
    v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_66,c_140])).

tff(c_70,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_68,plain,(
    v1_funct_2('#skF_7','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_744,plain,(
    ! [A_138,B_139,C_140] :
      ( k1_relset_1(A_138,B_139,C_140) = k1_relat_1(C_140)
      | ~ m1_subset_1(C_140,k1_zfmisc_1(k2_zfmisc_1(A_138,B_139))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_767,plain,(
    k1_relset_1('#skF_5','#skF_6','#skF_7') = k1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_66,c_744])).

tff(c_1150,plain,(
    ! [B_196,A_197,C_198] :
      ( k1_xboole_0 = B_196
      | k1_relset_1(A_197,B_196,C_198) = A_197
      | ~ v1_funct_2(C_198,A_197,B_196)
      | ~ m1_subset_1(C_198,k1_zfmisc_1(k2_zfmisc_1(A_197,B_196))) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_1164,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_relset_1('#skF_5','#skF_6','#skF_7') = '#skF_5'
    | ~ v1_funct_2('#skF_7','#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_66,c_1150])).

tff(c_1182,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_relat_1('#skF_7') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_767,c_1164])).

tff(c_1194,plain,(
    k1_relat_1('#skF_7') = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_1182])).

tff(c_160,plain,(
    v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_60,c_140])).

tff(c_64,plain,(
    v1_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_62,plain,(
    v1_funct_2('#skF_8','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_766,plain,(
    k1_relset_1('#skF_5','#skF_6','#skF_8') = k1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_60,c_744])).

tff(c_1161,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_relset_1('#skF_5','#skF_6','#skF_8') = '#skF_5'
    | ~ v1_funct_2('#skF_8','#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_60,c_1150])).

tff(c_1179,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_relat_1('#skF_8') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_766,c_1161])).

tff(c_1188,plain,(
    k1_relat_1('#skF_8') = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_1179])).

tff(c_1402,plain,(
    ! [A_212,B_213] :
      ( r2_hidden('#skF_2'(A_212,B_213),k1_relat_1(A_212))
      | B_213 = A_212
      | k1_relat_1(B_213) != k1_relat_1(A_212)
      | ~ v1_funct_1(B_213)
      | ~ v1_relat_1(B_213)
      | ~ v1_funct_1(A_212)
      | ~ v1_relat_1(A_212) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_1420,plain,(
    ! [B_213] :
      ( r2_hidden('#skF_2'('#skF_8',B_213),'#skF_5')
      | B_213 = '#skF_8'
      | k1_relat_1(B_213) != k1_relat_1('#skF_8')
      | ~ v1_funct_1(B_213)
      | ~ v1_relat_1(B_213)
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1188,c_1402])).

tff(c_1446,plain,(
    ! [B_215] :
      ( r2_hidden('#skF_2'('#skF_8',B_215),'#skF_5')
      | B_215 = '#skF_8'
      | k1_relat_1(B_215) != '#skF_5'
      | ~ v1_funct_1(B_215)
      | ~ v1_relat_1(B_215) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_160,c_64,c_1188,c_1420])).

tff(c_18,plain,(
    ! [A_11,B_12] :
      ( m1_subset_1(A_11,B_12)
      | ~ r2_hidden(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1494,plain,(
    ! [B_222] :
      ( m1_subset_1('#skF_2'('#skF_8',B_222),'#skF_5')
      | B_222 = '#skF_8'
      | k1_relat_1(B_222) != '#skF_5'
      | ~ v1_funct_1(B_222)
      | ~ v1_relat_1(B_222) ) ),
    inference(resolution,[status(thm)],[c_1446,c_18])).

tff(c_58,plain,(
    ! [E_51] :
      ( k1_funct_1('#skF_7',E_51) = k1_funct_1('#skF_8',E_51)
      | ~ m1_subset_1(E_51,'#skF_5') ) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_1674,plain,(
    ! [B_249] :
      ( k1_funct_1('#skF_7','#skF_2'('#skF_8',B_249)) = k1_funct_1('#skF_8','#skF_2'('#skF_8',B_249))
      | B_249 = '#skF_8'
      | k1_relat_1(B_249) != '#skF_5'
      | ~ v1_funct_1(B_249)
      | ~ v1_relat_1(B_249) ) ),
    inference(resolution,[status(thm)],[c_1494,c_58])).

tff(c_22,plain,(
    ! [B_20,A_16] :
      ( k1_funct_1(B_20,'#skF_2'(A_16,B_20)) != k1_funct_1(A_16,'#skF_2'(A_16,B_20))
      | B_20 = A_16
      | k1_relat_1(B_20) != k1_relat_1(A_16)
      | ~ v1_funct_1(B_20)
      | ~ v1_relat_1(B_20)
      | ~ v1_funct_1(A_16)
      | ~ v1_relat_1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_1681,plain,
    ( k1_relat_1('#skF_7') != k1_relat_1('#skF_8')
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8')
    | '#skF_7' = '#skF_8'
    | k1_relat_1('#skF_7') != '#skF_5'
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_1674,c_22])).

tff(c_1688,plain,(
    '#skF_7' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_161,c_70,c_1194,c_160,c_64,c_1194,c_1188,c_1681])).

tff(c_56,plain,(
    ~ r2_relset_1('#skF_5','#skF_6','#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_1712,plain,(
    ~ r2_relset_1('#skF_5','#skF_6','#skF_8','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1688,c_56])).

tff(c_1722,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_738,c_1712])).

tff(c_1723,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_1182])).

tff(c_6,plain,(
    ! [A_5] : r1_tarski(k1_xboole_0,A_5) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_108,plain,(
    ! [B_62,A_63] :
      ( ~ r1_tarski(B_62,A_63)
      | ~ r2_hidden(A_63,B_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_119,plain,(
    ! [A_67] :
      ( ~ r1_tarski(A_67,'#skF_1'(A_67))
      | v1_xboole_0(A_67) ) ),
    inference(resolution,[status(thm)],[c_4,c_108])).

tff(c_124,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_6,c_119])).

tff(c_1747,plain,(
    v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1723,c_124])).

tff(c_1754,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_685,c_1747])).

tff(c_1755,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_1179])).

tff(c_1816,plain,(
    v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1755,c_124])).

tff(c_1823,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_685,c_1816])).

tff(c_1824,plain,(
    v1_xboole_0('#skF_8') ),
    inference(splitRight,[status(thm)],[c_678])).

tff(c_8,plain,(
    ! [B_7,A_6] :
      ( ~ v1_xboole_0(B_7)
      | B_7 = A_6
      | ~ v1_xboole_0(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_133,plain,(
    ! [A_6] :
      ( k1_xboole_0 = A_6
      | ~ v1_xboole_0(A_6) ) ),
    inference(resolution,[status(thm)],[c_124,c_8])).

tff(c_1831,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(resolution,[status(thm)],[c_1824,c_133])).

tff(c_16,plain,(
    ! [A_10] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_10)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1967,plain,(
    ! [A_263] : m1_subset_1('#skF_8',k1_zfmisc_1(A_263)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1831,c_16])).

tff(c_34,plain,(
    ! [A_34,B_35,D_37] :
      ( r2_relset_1(A_34,B_35,D_37,D_37)
      | ~ m1_subset_1(D_37,k1_zfmisc_1(k2_zfmisc_1(A_34,B_35))) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_1983,plain,(
    ! [A_34,B_35] : r2_relset_1(A_34,B_35,'#skF_8','#skF_8') ),
    inference(resolution,[status(thm)],[c_1967,c_34])).

tff(c_1825,plain,(
    v1_xboole_0('#skF_6') ),
    inference(splitRight,[status(thm)],[c_678])).

tff(c_679,plain,
    ( v1_xboole_0('#skF_7')
    | ~ v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_66,c_656])).

tff(c_1841,plain,(
    v1_xboole_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1825,c_679])).

tff(c_1847,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(resolution,[status(thm)],[c_1841,c_133])).

tff(c_1879,plain,(
    '#skF_7' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1831,c_1847])).

tff(c_1838,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_1825,c_133])).

tff(c_1867,plain,(
    '#skF_6' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1831,c_1838])).

tff(c_1871,plain,(
    ~ r2_relset_1('#skF_5','#skF_8','#skF_7','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1867,c_56])).

tff(c_1990,plain,(
    ~ r2_relset_1('#skF_5','#skF_8','#skF_8','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1879,c_1871])).

tff(c_2019,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1983,c_1990])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:39:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.14/1.70  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.14/1.71  
% 4.14/1.71  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.14/1.71  %$ r2_relset_1 > v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_4 > #skF_8 > #skF_2 > #skF_3
% 4.14/1.71  
% 4.14/1.71  %Foreground sorts:
% 4.14/1.71  
% 4.14/1.71  
% 4.14/1.71  %Background operators:
% 4.14/1.71  
% 4.14/1.71  
% 4.14/1.71  %Foreground operators:
% 4.14/1.71  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.14/1.71  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.14/1.71  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 4.14/1.71  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.14/1.71  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 4.14/1.71  tff('#skF_1', type, '#skF_1': $i > $i).
% 4.14/1.71  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.14/1.71  tff('#skF_7', type, '#skF_7': $i).
% 4.14/1.71  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.14/1.71  tff('#skF_5', type, '#skF_5': $i).
% 4.14/1.71  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.14/1.71  tff('#skF_6', type, '#skF_6': $i).
% 4.14/1.71  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 4.14/1.71  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.14/1.71  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 4.14/1.71  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 4.14/1.71  tff('#skF_8', type, '#skF_8': $i).
% 4.14/1.71  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.14/1.71  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.14/1.71  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.14/1.71  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.14/1.71  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.14/1.71  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 4.14/1.71  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.14/1.71  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.14/1.71  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.14/1.71  
% 4.14/1.73  tff(f_157, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((![E]: (m1_subset_1(E, A) => (k1_funct_1(C, E) = k1_funct_1(D, E)))) => r2_relset_1(A, B, C, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_funct_2)).
% 4.14/1.73  tff(f_93, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => v1_xboole_0(C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc4_relset_1)).
% 4.14/1.73  tff(f_105, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 4.14/1.73  tff(f_86, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 4.14/1.73  tff(f_97, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 4.14/1.73  tff(f_136, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 4.14/1.73  tff(f_77, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((k1_relat_1(A) = k1_relat_1(B)) & (![C]: (r2_hidden(C, k1_relat_1(A)) => (k1_funct_1(A, C) = k1_funct_1(B, C))))) => (A = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_funct_1)).
% 4.14/1.73  tff(f_53, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 4.14/1.73  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 4.14/1.73  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 4.14/1.73  tff(f_82, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 4.14/1.73  tff(f_41, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_boole)).
% 4.14/1.73  tff(f_49, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 4.14/1.73  tff(c_60, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_157])).
% 4.14/1.73  tff(c_656, plain, (![C_122, B_123, A_124]: (v1_xboole_0(C_122) | ~m1_subset_1(C_122, k1_zfmisc_1(k2_zfmisc_1(B_123, A_124))) | ~v1_xboole_0(A_124))), inference(cnfTransformation, [status(thm)], [f_93])).
% 4.14/1.73  tff(c_678, plain, (v1_xboole_0('#skF_8') | ~v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_60, c_656])).
% 4.14/1.73  tff(c_685, plain, (~v1_xboole_0('#skF_6')), inference(splitLeft, [status(thm)], [c_678])).
% 4.14/1.73  tff(c_722, plain, (![A_133, B_134, D_135]: (r2_relset_1(A_133, B_134, D_135, D_135) | ~m1_subset_1(D_135, k1_zfmisc_1(k2_zfmisc_1(A_133, B_134))))), inference(cnfTransformation, [status(thm)], [f_105])).
% 4.14/1.73  tff(c_738, plain, (r2_relset_1('#skF_5', '#skF_6', '#skF_8', '#skF_8')), inference(resolution, [status(thm)], [c_60, c_722])).
% 4.14/1.73  tff(c_66, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_157])).
% 4.14/1.73  tff(c_140, plain, (![C_70, A_71, B_72]: (v1_relat_1(C_70) | ~m1_subset_1(C_70, k1_zfmisc_1(k2_zfmisc_1(A_71, B_72))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 4.14/1.73  tff(c_161, plain, (v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_66, c_140])).
% 4.14/1.73  tff(c_70, plain, (v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_157])).
% 4.14/1.73  tff(c_68, plain, (v1_funct_2('#skF_7', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_157])).
% 4.14/1.73  tff(c_744, plain, (![A_138, B_139, C_140]: (k1_relset_1(A_138, B_139, C_140)=k1_relat_1(C_140) | ~m1_subset_1(C_140, k1_zfmisc_1(k2_zfmisc_1(A_138, B_139))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 4.14/1.73  tff(c_767, plain, (k1_relset_1('#skF_5', '#skF_6', '#skF_7')=k1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_66, c_744])).
% 4.14/1.73  tff(c_1150, plain, (![B_196, A_197, C_198]: (k1_xboole_0=B_196 | k1_relset_1(A_197, B_196, C_198)=A_197 | ~v1_funct_2(C_198, A_197, B_196) | ~m1_subset_1(C_198, k1_zfmisc_1(k2_zfmisc_1(A_197, B_196))))), inference(cnfTransformation, [status(thm)], [f_136])).
% 4.14/1.73  tff(c_1164, plain, (k1_xboole_0='#skF_6' | k1_relset_1('#skF_5', '#skF_6', '#skF_7')='#skF_5' | ~v1_funct_2('#skF_7', '#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_66, c_1150])).
% 4.14/1.73  tff(c_1182, plain, (k1_xboole_0='#skF_6' | k1_relat_1('#skF_7')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_767, c_1164])).
% 4.14/1.73  tff(c_1194, plain, (k1_relat_1('#skF_7')='#skF_5'), inference(splitLeft, [status(thm)], [c_1182])).
% 4.14/1.73  tff(c_160, plain, (v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_60, c_140])).
% 4.14/1.73  tff(c_64, plain, (v1_funct_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_157])).
% 4.14/1.73  tff(c_62, plain, (v1_funct_2('#skF_8', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_157])).
% 4.14/1.73  tff(c_766, plain, (k1_relset_1('#skF_5', '#skF_6', '#skF_8')=k1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_60, c_744])).
% 4.14/1.73  tff(c_1161, plain, (k1_xboole_0='#skF_6' | k1_relset_1('#skF_5', '#skF_6', '#skF_8')='#skF_5' | ~v1_funct_2('#skF_8', '#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_60, c_1150])).
% 4.14/1.73  tff(c_1179, plain, (k1_xboole_0='#skF_6' | k1_relat_1('#skF_8')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_766, c_1161])).
% 4.14/1.73  tff(c_1188, plain, (k1_relat_1('#skF_8')='#skF_5'), inference(splitLeft, [status(thm)], [c_1179])).
% 4.14/1.73  tff(c_1402, plain, (![A_212, B_213]: (r2_hidden('#skF_2'(A_212, B_213), k1_relat_1(A_212)) | B_213=A_212 | k1_relat_1(B_213)!=k1_relat_1(A_212) | ~v1_funct_1(B_213) | ~v1_relat_1(B_213) | ~v1_funct_1(A_212) | ~v1_relat_1(A_212))), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.14/1.73  tff(c_1420, plain, (![B_213]: (r2_hidden('#skF_2'('#skF_8', B_213), '#skF_5') | B_213='#skF_8' | k1_relat_1(B_213)!=k1_relat_1('#skF_8') | ~v1_funct_1(B_213) | ~v1_relat_1(B_213) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_1188, c_1402])).
% 4.14/1.73  tff(c_1446, plain, (![B_215]: (r2_hidden('#skF_2'('#skF_8', B_215), '#skF_5') | B_215='#skF_8' | k1_relat_1(B_215)!='#skF_5' | ~v1_funct_1(B_215) | ~v1_relat_1(B_215))), inference(demodulation, [status(thm), theory('equality')], [c_160, c_64, c_1188, c_1420])).
% 4.14/1.73  tff(c_18, plain, (![A_11, B_12]: (m1_subset_1(A_11, B_12) | ~r2_hidden(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.14/1.73  tff(c_1494, plain, (![B_222]: (m1_subset_1('#skF_2'('#skF_8', B_222), '#skF_5') | B_222='#skF_8' | k1_relat_1(B_222)!='#skF_5' | ~v1_funct_1(B_222) | ~v1_relat_1(B_222))), inference(resolution, [status(thm)], [c_1446, c_18])).
% 4.14/1.73  tff(c_58, plain, (![E_51]: (k1_funct_1('#skF_7', E_51)=k1_funct_1('#skF_8', E_51) | ~m1_subset_1(E_51, '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_157])).
% 4.14/1.73  tff(c_1674, plain, (![B_249]: (k1_funct_1('#skF_7', '#skF_2'('#skF_8', B_249))=k1_funct_1('#skF_8', '#skF_2'('#skF_8', B_249)) | B_249='#skF_8' | k1_relat_1(B_249)!='#skF_5' | ~v1_funct_1(B_249) | ~v1_relat_1(B_249))), inference(resolution, [status(thm)], [c_1494, c_58])).
% 4.14/1.73  tff(c_22, plain, (![B_20, A_16]: (k1_funct_1(B_20, '#skF_2'(A_16, B_20))!=k1_funct_1(A_16, '#skF_2'(A_16, B_20)) | B_20=A_16 | k1_relat_1(B_20)!=k1_relat_1(A_16) | ~v1_funct_1(B_20) | ~v1_relat_1(B_20) | ~v1_funct_1(A_16) | ~v1_relat_1(A_16))), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.14/1.73  tff(c_1681, plain, (k1_relat_1('#skF_7')!=k1_relat_1('#skF_8') | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8') | '#skF_7'='#skF_8' | k1_relat_1('#skF_7')!='#skF_5' | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_1674, c_22])).
% 4.14/1.73  tff(c_1688, plain, ('#skF_7'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_161, c_70, c_1194, c_160, c_64, c_1194, c_1188, c_1681])).
% 4.14/1.73  tff(c_56, plain, (~r2_relset_1('#skF_5', '#skF_6', '#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_157])).
% 4.14/1.73  tff(c_1712, plain, (~r2_relset_1('#skF_5', '#skF_6', '#skF_8', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_1688, c_56])).
% 4.14/1.73  tff(c_1722, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_738, c_1712])).
% 4.14/1.73  tff(c_1723, plain, (k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_1182])).
% 4.14/1.73  tff(c_6, plain, (![A_5]: (r1_tarski(k1_xboole_0, A_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.14/1.73  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.14/1.73  tff(c_108, plain, (![B_62, A_63]: (~r1_tarski(B_62, A_63) | ~r2_hidden(A_63, B_62))), inference(cnfTransformation, [status(thm)], [f_82])).
% 4.14/1.73  tff(c_119, plain, (![A_67]: (~r1_tarski(A_67, '#skF_1'(A_67)) | v1_xboole_0(A_67))), inference(resolution, [status(thm)], [c_4, c_108])).
% 4.14/1.73  tff(c_124, plain, (v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_119])).
% 4.14/1.73  tff(c_1747, plain, (v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_1723, c_124])).
% 4.14/1.73  tff(c_1754, plain, $false, inference(negUnitSimplification, [status(thm)], [c_685, c_1747])).
% 4.14/1.73  tff(c_1755, plain, (k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_1179])).
% 4.14/1.73  tff(c_1816, plain, (v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_1755, c_124])).
% 4.14/1.73  tff(c_1823, plain, $false, inference(negUnitSimplification, [status(thm)], [c_685, c_1816])).
% 4.14/1.73  tff(c_1824, plain, (v1_xboole_0('#skF_8')), inference(splitRight, [status(thm)], [c_678])).
% 4.14/1.73  tff(c_8, plain, (![B_7, A_6]: (~v1_xboole_0(B_7) | B_7=A_6 | ~v1_xboole_0(A_6))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.14/1.73  tff(c_133, plain, (![A_6]: (k1_xboole_0=A_6 | ~v1_xboole_0(A_6))), inference(resolution, [status(thm)], [c_124, c_8])).
% 4.14/1.73  tff(c_1831, plain, (k1_xboole_0='#skF_8'), inference(resolution, [status(thm)], [c_1824, c_133])).
% 4.14/1.73  tff(c_16, plain, (![A_10]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_10)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.14/1.73  tff(c_1967, plain, (![A_263]: (m1_subset_1('#skF_8', k1_zfmisc_1(A_263)))), inference(demodulation, [status(thm), theory('equality')], [c_1831, c_16])).
% 4.14/1.73  tff(c_34, plain, (![A_34, B_35, D_37]: (r2_relset_1(A_34, B_35, D_37, D_37) | ~m1_subset_1(D_37, k1_zfmisc_1(k2_zfmisc_1(A_34, B_35))))), inference(cnfTransformation, [status(thm)], [f_105])).
% 4.14/1.73  tff(c_1983, plain, (![A_34, B_35]: (r2_relset_1(A_34, B_35, '#skF_8', '#skF_8'))), inference(resolution, [status(thm)], [c_1967, c_34])).
% 4.14/1.73  tff(c_1825, plain, (v1_xboole_0('#skF_6')), inference(splitRight, [status(thm)], [c_678])).
% 4.14/1.73  tff(c_679, plain, (v1_xboole_0('#skF_7') | ~v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_66, c_656])).
% 4.14/1.73  tff(c_1841, plain, (v1_xboole_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_1825, c_679])).
% 4.14/1.73  tff(c_1847, plain, (k1_xboole_0='#skF_7'), inference(resolution, [status(thm)], [c_1841, c_133])).
% 4.14/1.73  tff(c_1879, plain, ('#skF_7'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_1831, c_1847])).
% 4.14/1.73  tff(c_1838, plain, (k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_1825, c_133])).
% 4.14/1.73  tff(c_1867, plain, ('#skF_6'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_1831, c_1838])).
% 4.14/1.73  tff(c_1871, plain, (~r2_relset_1('#skF_5', '#skF_8', '#skF_7', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_1867, c_56])).
% 4.14/1.73  tff(c_1990, plain, (~r2_relset_1('#skF_5', '#skF_8', '#skF_8', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_1879, c_1871])).
% 4.14/1.73  tff(c_2019, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1983, c_1990])).
% 4.14/1.73  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.14/1.73  
% 4.14/1.73  Inference rules
% 4.14/1.73  ----------------------
% 4.14/1.73  #Ref     : 1
% 4.14/1.73  #Sup     : 399
% 4.14/1.73  #Fact    : 0
% 4.14/1.73  #Define  : 0
% 4.14/1.73  #Split   : 13
% 4.14/1.73  #Chain   : 0
% 4.14/1.73  #Close   : 0
% 4.14/1.73  
% 4.14/1.73  Ordering : KBO
% 4.14/1.73  
% 4.14/1.73  Simplification rules
% 4.14/1.73  ----------------------
% 4.14/1.73  #Subsume      : 77
% 4.14/1.73  #Demod        : 554
% 4.14/1.73  #Tautology    : 207
% 4.14/1.73  #SimpNegUnit  : 9
% 4.14/1.73  #BackRed      : 143
% 4.14/1.73  
% 4.14/1.73  #Partial instantiations: 0
% 4.14/1.73  #Strategies tried      : 1
% 4.14/1.73  
% 4.14/1.73  Timing (in seconds)
% 4.14/1.73  ----------------------
% 4.14/1.73  Preprocessing        : 0.35
% 4.14/1.73  Parsing              : 0.18
% 4.14/1.73  CNF conversion       : 0.03
% 4.14/1.73  Main loop            : 0.60
% 4.14/1.73  Inferencing          : 0.21
% 4.14/1.73  Reduction            : 0.20
% 4.14/1.73  Demodulation         : 0.14
% 4.14/1.73  BG Simplification    : 0.03
% 4.14/1.73  Subsumption          : 0.11
% 4.14/1.73  Abstraction          : 0.03
% 4.14/1.73  MUC search           : 0.00
% 4.14/1.73  Cooper               : 0.00
% 4.14/1.73  Total                : 0.99
% 4.14/1.73  Index Insertion      : 0.00
% 4.14/1.73  Index Deletion       : 0.00
% 4.14/1.73  Index Matching       : 0.00
% 4.14/1.73  BG Taut test         : 0.00
%------------------------------------------------------------------------------
