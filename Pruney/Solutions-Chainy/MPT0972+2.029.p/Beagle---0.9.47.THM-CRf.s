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
% DateTime   : Thu Dec  3 10:11:38 EST 2020

% Result     : Theorem 4.97s
% Output     : CNFRefutation 5.44s
% Verified   : 
% Statistics : Number of formulae       :  167 (1277 expanded)
%              Number of leaves         :   31 ( 424 expanded)
%              Depth                    :   16
%              Number of atoms          :  323 (3837 expanded)
%              Number of equality atoms :  138 (1061 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

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

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_120,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [D] :
            ( ( v1_funct_1(D)
              & v1_funct_2(D,A,B)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
           => ( ! [E] :
                  ( r2_hidden(E,A)
                 => k1_funct_1(C,E) = k1_funct_1(D,E) )
             => r2_relset_1(A,B,C,D) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_funct_2)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_81,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => r2_relset_1(A,B,C,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_99,axiom,(
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

tff(f_67,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_funct_1)).

tff(f_39,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_37,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_48,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_139,plain,(
    ! [C_49,A_50,B_51] :
      ( v1_relat_1(C_49)
      | ~ m1_subset_1(C_49,k1_zfmisc_1(k2_zfmisc_1(A_50,B_51))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_160,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_48,c_139])).

tff(c_52,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_50,plain,(
    v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_54,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_524,plain,(
    ! [A_107,B_108,C_109,D_110] :
      ( r2_relset_1(A_107,B_108,C_109,C_109)
      | ~ m1_subset_1(D_110,k1_zfmisc_1(k2_zfmisc_1(A_107,B_108)))
      | ~ m1_subset_1(C_109,k1_zfmisc_1(k2_zfmisc_1(A_107,B_108))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_544,plain,(
    ! [C_111] :
      ( r2_relset_1('#skF_2','#skF_3',C_111,C_111)
      | ~ m1_subset_1(C_111,k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ) ),
    inference(resolution,[status(thm)],[c_54,c_524])).

tff(c_556,plain,(
    r2_relset_1('#skF_2','#skF_3','#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_54,c_544])).

tff(c_246,plain,(
    ! [A_64,B_65,C_66] :
      ( k1_relset_1(A_64,B_65,C_66) = k1_relat_1(C_66)
      | ~ m1_subset_1(C_66,k1_zfmisc_1(k2_zfmisc_1(A_64,B_65))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_269,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_48,c_246])).

tff(c_447,plain,(
    ! [B_100,A_101,C_102] :
      ( k1_xboole_0 = B_100
      | k1_relset_1(A_101,B_100,C_102) = A_101
      | ~ v1_funct_2(C_102,A_101,B_100)
      | ~ m1_subset_1(C_102,k1_zfmisc_1(k2_zfmisc_1(A_101,B_100))) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_457,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_2'
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_447])).

tff(c_474,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_269,c_457])).

tff(c_484,plain,(
    k1_relat_1('#skF_5') = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_474])).

tff(c_159,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_54,c_139])).

tff(c_58,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_56,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_268,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_54,c_246])).

tff(c_454,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_4') = '#skF_2'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_54,c_447])).

tff(c_471,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_268,c_454])).

tff(c_478,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_471])).

tff(c_600,plain,(
    ! [A_118,B_119] :
      ( r2_hidden('#skF_1'(A_118,B_119),k1_relat_1(A_118))
      | B_119 = A_118
      | k1_relat_1(B_119) != k1_relat_1(A_118)
      | ~ v1_funct_1(B_119)
      | ~ v1_relat_1(B_119)
      | ~ v1_funct_1(A_118)
      | ~ v1_relat_1(A_118) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_608,plain,(
    ! [B_119] :
      ( r2_hidden('#skF_1'('#skF_4',B_119),'#skF_2')
      | B_119 = '#skF_4'
      | k1_relat_1(B_119) != k1_relat_1('#skF_4')
      | ~ v1_funct_1(B_119)
      | ~ v1_relat_1(B_119)
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_478,c_600])).

tff(c_635,plain,(
    ! [B_126] :
      ( r2_hidden('#skF_1'('#skF_4',B_126),'#skF_2')
      | B_126 = '#skF_4'
      | k1_relat_1(B_126) != '#skF_2'
      | ~ v1_funct_1(B_126)
      | ~ v1_relat_1(B_126) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_159,c_58,c_478,c_608])).

tff(c_46,plain,(
    ! [E_34] :
      ( k1_funct_1('#skF_5',E_34) = k1_funct_1('#skF_4',E_34)
      | ~ r2_hidden(E_34,'#skF_2') ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_989,plain,(
    ! [B_155] :
      ( k1_funct_1('#skF_5','#skF_1'('#skF_4',B_155)) = k1_funct_1('#skF_4','#skF_1'('#skF_4',B_155))
      | B_155 = '#skF_4'
      | k1_relat_1(B_155) != '#skF_2'
      | ~ v1_funct_1(B_155)
      | ~ v1_relat_1(B_155) ) ),
    inference(resolution,[status(thm)],[c_635,c_46])).

tff(c_22,plain,(
    ! [B_15,A_11] :
      ( k1_funct_1(B_15,'#skF_1'(A_11,B_15)) != k1_funct_1(A_11,'#skF_1'(A_11,B_15))
      | B_15 = A_11
      | k1_relat_1(B_15) != k1_relat_1(A_11)
      | ~ v1_funct_1(B_15)
      | ~ v1_relat_1(B_15)
      | ~ v1_funct_1(A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_996,plain,
    ( k1_relat_1('#skF_5') != k1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4')
    | '#skF_5' = '#skF_4'
    | k1_relat_1('#skF_5') != '#skF_2'
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_989,c_22])).

tff(c_1003,plain,(
    '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_160,c_52,c_484,c_159,c_58,c_484,c_478,c_996])).

tff(c_44,plain,(
    ~ r2_relset_1('#skF_2','#skF_3','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_1018,plain,(
    ~ r2_relset_1('#skF_2','#skF_3','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1003,c_44])).

tff(c_1029,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_556,c_1018])).

tff(c_1030,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_474])).

tff(c_14,plain,(
    ! [A_5] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_5)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_91,plain,(
    ! [A_42,B_43] :
      ( r1_tarski(A_42,B_43)
      | ~ m1_subset_1(A_42,k1_zfmisc_1(B_43)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_107,plain,(
    ! [A_5] : r1_tarski(k1_xboole_0,A_5) ),
    inference(resolution,[status(thm)],[c_14,c_91])).

tff(c_1050,plain,(
    ! [A_5] : r1_tarski('#skF_3',A_5) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1030,c_107])).

tff(c_10,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1053,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1030,c_1030,c_10])).

tff(c_105,plain,(
    r1_tarski('#skF_4',k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_54,c_91])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_121,plain,
    ( k2_zfmisc_1('#skF_2','#skF_3') = '#skF_4'
    | ~ r1_tarski(k2_zfmisc_1('#skF_2','#skF_3'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_105,c_2])).

tff(c_232,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_2','#skF_3'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_121])).

tff(c_1153,plain,(
    ~ r1_tarski('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1053,c_232])).

tff(c_1161,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1050,c_1153])).

tff(c_1162,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_471])).

tff(c_1182,plain,(
    ! [A_5] : r1_tarski('#skF_3',A_5) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1162,c_107])).

tff(c_1185,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1162,c_1162,c_10])).

tff(c_1285,plain,(
    ~ r1_tarski('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1185,c_232])).

tff(c_1293,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1182,c_1285])).

tff(c_1294,plain,(
    k2_zfmisc_1('#skF_2','#skF_3') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_121])).

tff(c_1300,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1294,c_48])).

tff(c_1395,plain,(
    ! [A_186,B_187,C_188] :
      ( k1_relset_1(A_186,B_187,C_188) = k1_relat_1(C_188)
      | ~ m1_subset_1(C_188,k1_zfmisc_1(k2_zfmisc_1(A_186,B_187))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_1415,plain,(
    ! [C_189] :
      ( k1_relset_1('#skF_2','#skF_3',C_189) = k1_relat_1(C_189)
      | ~ m1_subset_1(C_189,k1_zfmisc_1('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1294,c_1395])).

tff(c_1430,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_1300,c_1415])).

tff(c_1489,plain,(
    ! [B_197,C_198,A_199] :
      ( k1_xboole_0 = B_197
      | v1_funct_2(C_198,A_199,B_197)
      | k1_relset_1(A_199,B_197,C_198) != A_199
      | ~ m1_subset_1(C_198,k1_zfmisc_1(k2_zfmisc_1(A_199,B_197))) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_1492,plain,(
    ! [C_198] :
      ( k1_xboole_0 = '#skF_3'
      | v1_funct_2(C_198,'#skF_2','#skF_3')
      | k1_relset_1('#skF_2','#skF_3',C_198) != '#skF_2'
      | ~ m1_subset_1(C_198,k1_zfmisc_1('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1294,c_1489])).

tff(c_1618,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_1492])).

tff(c_8,plain,(
    ! [B_4,A_3] :
      ( k1_xboole_0 = B_4
      | k1_xboole_0 = A_3
      | k2_zfmisc_1(A_3,B_4) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1309,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 != '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_1294,c_8])).

tff(c_1385,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_1309])).

tff(c_1631,plain,(
    '#skF_3' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1618,c_1385])).

tff(c_1711,plain,(
    ! [A_222] : k2_zfmisc_1(A_222,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1618,c_1618,c_10])).

tff(c_1730,plain,(
    '#skF_3' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_1711,c_1294])).

tff(c_1749,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1631,c_1730])).

tff(c_1751,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_1492])).

tff(c_1828,plain,(
    ! [B_230,A_231,C_232] :
      ( k1_xboole_0 = B_230
      | k1_relset_1(A_231,B_230,C_232) = A_231
      | ~ v1_funct_2(C_232,A_231,B_230)
      | ~ m1_subset_1(C_232,k1_zfmisc_1(k2_zfmisc_1(A_231,B_230))) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_1831,plain,(
    ! [C_232] :
      ( k1_xboole_0 = '#skF_3'
      | k1_relset_1('#skF_2','#skF_3',C_232) = '#skF_2'
      | ~ v1_funct_2(C_232,'#skF_2','#skF_3')
      | ~ m1_subset_1(C_232,k1_zfmisc_1('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1294,c_1828])).

tff(c_1994,plain,(
    ! [C_261] :
      ( k1_relset_1('#skF_2','#skF_3',C_261) = '#skF_2'
      | ~ v1_funct_2(C_261,'#skF_2','#skF_3')
      | ~ m1_subset_1(C_261,k1_zfmisc_1('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_1751,c_1831])).

tff(c_1997,plain,
    ( k1_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_2'
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_1300,c_1994])).

tff(c_2011,plain,(
    k1_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_1430,c_1997])).

tff(c_1299,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1294,c_54])).

tff(c_1431,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_1299,c_1415])).

tff(c_2000,plain,
    ( k1_relset_1('#skF_2','#skF_3','#skF_4') = '#skF_2'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_1299,c_1994])).

tff(c_2014,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_1431,c_2000])).

tff(c_24,plain,(
    ! [A_11,B_15] :
      ( r2_hidden('#skF_1'(A_11,B_15),k1_relat_1(A_11))
      | B_15 = A_11
      | k1_relat_1(B_15) != k1_relat_1(A_11)
      | ~ v1_funct_1(B_15)
      | ~ v1_relat_1(B_15)
      | ~ v1_funct_1(A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_2039,plain,(
    ! [B_15] :
      ( r2_hidden('#skF_1'('#skF_4',B_15),'#skF_2')
      | B_15 = '#skF_4'
      | k1_relat_1(B_15) != k1_relat_1('#skF_4')
      | ~ v1_funct_1(B_15)
      | ~ v1_relat_1(B_15)
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2014,c_24])).

tff(c_2097,plain,(
    ! [B_265] :
      ( r2_hidden('#skF_1'('#skF_4',B_265),'#skF_2')
      | B_265 = '#skF_4'
      | k1_relat_1(B_265) != '#skF_2'
      | ~ v1_funct_1(B_265)
      | ~ v1_relat_1(B_265) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_159,c_58,c_2014,c_2039])).

tff(c_2473,plain,(
    ! [B_285] :
      ( k1_funct_1('#skF_5','#skF_1'('#skF_4',B_285)) = k1_funct_1('#skF_4','#skF_1'('#skF_4',B_285))
      | B_285 = '#skF_4'
      | k1_relat_1(B_285) != '#skF_2'
      | ~ v1_funct_1(B_285)
      | ~ v1_relat_1(B_285) ) ),
    inference(resolution,[status(thm)],[c_2097,c_46])).

tff(c_2480,plain,
    ( k1_relat_1('#skF_5') != k1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4')
    | '#skF_5' = '#skF_4'
    | k1_relat_1('#skF_5') != '#skF_2'
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_2473,c_22])).

tff(c_2487,plain,(
    '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_160,c_52,c_2011,c_159,c_58,c_2014,c_2011,c_2480])).

tff(c_106,plain,(
    r1_tarski('#skF_5',k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_48,c_91])).

tff(c_124,plain,
    ( k2_zfmisc_1('#skF_2','#skF_3') = '#skF_5'
    | ~ r1_tarski(k2_zfmisc_1('#skF_2','#skF_3'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_106,c_2])).

tff(c_224,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_2','#skF_3'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_124])).

tff(c_1296,plain,(
    ~ r1_tarski('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1294,c_224])).

tff(c_2498,plain,(
    ~ r1_tarski('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2487,c_1296])).

tff(c_2511,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_2498])).

tff(c_2513,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_1309])).

tff(c_2520,plain,(
    ! [A_5] : r1_tarski('#skF_4',A_5) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2513,c_107])).

tff(c_2532,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2520,c_1296])).

tff(c_2533,plain,(
    k2_zfmisc_1('#skF_2','#skF_3') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_124])).

tff(c_2545,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2533,c_48])).

tff(c_2609,plain,(
    ! [A_295,B_296,C_297] :
      ( k1_relset_1(A_295,B_296,C_297) = k1_relat_1(C_297)
      | ~ m1_subset_1(C_297,k1_zfmisc_1(k2_zfmisc_1(A_295,B_296))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_2711,plain,(
    ! [C_315] :
      ( k1_relset_1('#skF_2','#skF_3',C_315) = k1_relat_1(C_315)
      | ~ m1_subset_1(C_315,k1_zfmisc_1('#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2533,c_2609])).

tff(c_2727,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_2545,c_2711])).

tff(c_2826,plain,(
    ! [B_328,A_329,C_330] :
      ( k1_xboole_0 = B_328
      | k1_relset_1(A_329,B_328,C_330) = A_329
      | ~ v1_funct_2(C_330,A_329,B_328)
      | ~ m1_subset_1(C_330,k1_zfmisc_1(k2_zfmisc_1(A_329,B_328))) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_2829,plain,(
    ! [C_330] :
      ( k1_xboole_0 = '#skF_3'
      | k1_relset_1('#skF_2','#skF_3',C_330) = '#skF_2'
      | ~ v1_funct_2(C_330,'#skF_2','#skF_3')
      | ~ m1_subset_1(C_330,k1_zfmisc_1('#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2533,c_2826])).

tff(c_2862,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_2829])).

tff(c_2554,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 != '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_2533,c_8])).

tff(c_2637,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_2554])).

tff(c_2874,plain,(
    '#skF_5' != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2862,c_2637])).

tff(c_2885,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2862,c_2862,c_10])).

tff(c_2968,plain,(
    '#skF_5' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2885,c_2533])).

tff(c_2970,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2874,c_2968])).

tff(c_2973,plain,(
    ! [C_338] :
      ( k1_relset_1('#skF_2','#skF_3',C_338) = '#skF_2'
      | ~ v1_funct_2(C_338,'#skF_2','#skF_3')
      | ~ m1_subset_1(C_338,k1_zfmisc_1('#skF_5')) ) ),
    inference(splitRight,[status(thm)],[c_2829])).

tff(c_2979,plain,
    ( k1_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_2'
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_2545,c_2973])).

tff(c_2993,plain,(
    k1_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_2727,c_2979])).

tff(c_2544,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2533,c_54])).

tff(c_2726,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_2544,c_2711])).

tff(c_2976,plain,
    ( k1_relset_1('#skF_2','#skF_3','#skF_4') = '#skF_2'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_2544,c_2973])).

tff(c_2990,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_2726,c_2976])).

tff(c_3200,plain,(
    ! [A_364,B_365] :
      ( r2_hidden('#skF_1'(A_364,B_365),k1_relat_1(A_364))
      | B_365 = A_364
      | k1_relat_1(B_365) != k1_relat_1(A_364)
      | ~ v1_funct_1(B_365)
      | ~ v1_relat_1(B_365)
      | ~ v1_funct_1(A_364)
      | ~ v1_relat_1(A_364) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_3208,plain,(
    ! [B_365] :
      ( r2_hidden('#skF_1'('#skF_4',B_365),'#skF_2')
      | B_365 = '#skF_4'
      | k1_relat_1(B_365) != k1_relat_1('#skF_4')
      | ~ v1_funct_1(B_365)
      | ~ v1_relat_1(B_365)
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2990,c_3200])).

tff(c_3256,plain,(
    ! [B_373] :
      ( r2_hidden('#skF_1'('#skF_4',B_373),'#skF_2')
      | B_373 = '#skF_4'
      | k1_relat_1(B_373) != '#skF_2'
      | ~ v1_funct_1(B_373)
      | ~ v1_relat_1(B_373) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_159,c_58,c_2990,c_3208])).

tff(c_3643,plain,(
    ! [B_398] :
      ( k1_funct_1('#skF_5','#skF_1'('#skF_4',B_398)) = k1_funct_1('#skF_4','#skF_1'('#skF_4',B_398))
      | B_398 = '#skF_4'
      | k1_relat_1(B_398) != '#skF_2'
      | ~ v1_funct_1(B_398)
      | ~ v1_relat_1(B_398) ) ),
    inference(resolution,[status(thm)],[c_3256,c_46])).

tff(c_3650,plain,
    ( k1_relat_1('#skF_5') != k1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4')
    | '#skF_5' = '#skF_4'
    | k1_relat_1('#skF_5') != '#skF_2'
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_3643,c_22])).

tff(c_3657,plain,(
    '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_160,c_52,c_2993,c_159,c_58,c_2993,c_2990,c_3650])).

tff(c_2543,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2533,c_105])).

tff(c_2570,plain,
    ( '#skF_5' = '#skF_4'
    | ~ r1_tarski('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_2543,c_2])).

tff(c_2607,plain,(
    ~ r1_tarski('#skF_5','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_2570])).

tff(c_3678,plain,(
    ~ r1_tarski('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3657,c_2607])).

tff(c_3695,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_3678])).

tff(c_3697,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_2554])).

tff(c_3705,plain,(
    ! [A_5] : r1_tarski('#skF_5',A_5) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3697,c_107])).

tff(c_3717,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3705,c_2607])).

tff(c_3718,plain,(
    '#skF_5' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_2570])).

tff(c_3728,plain,(
    ~ r2_relset_1('#skF_2','#skF_3','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3718,c_44])).

tff(c_3722,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3718,c_2544])).

tff(c_3725,plain,(
    k2_zfmisc_1('#skF_2','#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3718,c_2533])).

tff(c_4170,plain,(
    ! [A_448,B_449,C_450,D_451] :
      ( r2_relset_1(A_448,B_449,C_450,C_450)
      | ~ m1_subset_1(D_451,k1_zfmisc_1(k2_zfmisc_1(A_448,B_449)))
      | ~ m1_subset_1(C_450,k1_zfmisc_1(k2_zfmisc_1(A_448,B_449))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_4187,plain,(
    ! [A_452,B_453,C_454] :
      ( r2_relset_1(A_452,B_453,C_454,C_454)
      | ~ m1_subset_1(C_454,k1_zfmisc_1(k2_zfmisc_1(A_452,B_453))) ) ),
    inference(resolution,[status(thm)],[c_14,c_4170])).

tff(c_4213,plain,(
    ! [C_459] :
      ( r2_relset_1('#skF_2','#skF_3',C_459,C_459)
      | ~ m1_subset_1(C_459,k1_zfmisc_1('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3725,c_4187])).

tff(c_4215,plain,(
    r2_relset_1('#skF_2','#skF_3','#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_3722,c_4213])).

tff(c_4225,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3728,c_4215])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:22:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.97/2.06  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.35/2.07  
% 5.35/2.07  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.35/2.08  %$ r2_relset_1 > v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 5.35/2.08  
% 5.35/2.08  %Foreground sorts:
% 5.35/2.08  
% 5.35/2.08  
% 5.35/2.08  %Background operators:
% 5.35/2.08  
% 5.35/2.08  
% 5.35/2.08  %Foreground operators:
% 5.35/2.08  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.35/2.08  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.35/2.08  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 5.35/2.08  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.35/2.08  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.35/2.08  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.35/2.08  tff('#skF_5', type, '#skF_5': $i).
% 5.35/2.08  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.35/2.08  tff('#skF_2', type, '#skF_2': $i).
% 5.35/2.08  tff('#skF_3', type, '#skF_3': $i).
% 5.35/2.08  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 5.35/2.08  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.35/2.08  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 5.35/2.08  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.35/2.08  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.35/2.08  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.35/2.08  tff('#skF_4', type, '#skF_4': $i).
% 5.35/2.08  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.35/2.08  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.35/2.08  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.35/2.08  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.35/2.08  
% 5.44/2.10  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.44/2.10  tff(f_120, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((![E]: (r2_hidden(E, A) => (k1_funct_1(C, E) = k1_funct_1(D, E)))) => r2_relset_1(A, B, C, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_funct_2)).
% 5.44/2.10  tff(f_71, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 5.44/2.10  tff(f_81, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r2_relset_1(A, B, C, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', reflexivity_r2_relset_1)).
% 5.44/2.10  tff(f_75, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 5.44/2.10  tff(f_99, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 5.44/2.10  tff(f_67, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((k1_relat_1(A) = k1_relat_1(B)) & (![C]: (r2_hidden(C, k1_relat_1(A)) => (k1_funct_1(A, C) = k1_funct_1(B, C))))) => (A = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_funct_1)).
% 5.44/2.10  tff(f_39, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 5.44/2.10  tff(f_43, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 5.44/2.10  tff(f_37, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 5.44/2.10  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.44/2.10  tff(c_48, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_120])).
% 5.44/2.10  tff(c_139, plain, (![C_49, A_50, B_51]: (v1_relat_1(C_49) | ~m1_subset_1(C_49, k1_zfmisc_1(k2_zfmisc_1(A_50, B_51))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 5.44/2.10  tff(c_160, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_48, c_139])).
% 5.44/2.10  tff(c_52, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_120])).
% 5.44/2.10  tff(c_50, plain, (v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_120])).
% 5.44/2.10  tff(c_54, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_120])).
% 5.44/2.10  tff(c_524, plain, (![A_107, B_108, C_109, D_110]: (r2_relset_1(A_107, B_108, C_109, C_109) | ~m1_subset_1(D_110, k1_zfmisc_1(k2_zfmisc_1(A_107, B_108))) | ~m1_subset_1(C_109, k1_zfmisc_1(k2_zfmisc_1(A_107, B_108))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 5.44/2.10  tff(c_544, plain, (![C_111]: (r2_relset_1('#skF_2', '#skF_3', C_111, C_111) | ~m1_subset_1(C_111, k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))))), inference(resolution, [status(thm)], [c_54, c_524])).
% 5.44/2.10  tff(c_556, plain, (r2_relset_1('#skF_2', '#skF_3', '#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_54, c_544])).
% 5.44/2.10  tff(c_246, plain, (![A_64, B_65, C_66]: (k1_relset_1(A_64, B_65, C_66)=k1_relat_1(C_66) | ~m1_subset_1(C_66, k1_zfmisc_1(k2_zfmisc_1(A_64, B_65))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 5.44/2.10  tff(c_269, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_48, c_246])).
% 5.44/2.10  tff(c_447, plain, (![B_100, A_101, C_102]: (k1_xboole_0=B_100 | k1_relset_1(A_101, B_100, C_102)=A_101 | ~v1_funct_2(C_102, A_101, B_100) | ~m1_subset_1(C_102, k1_zfmisc_1(k2_zfmisc_1(A_101, B_100))))), inference(cnfTransformation, [status(thm)], [f_99])).
% 5.44/2.10  tff(c_457, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_2' | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_48, c_447])).
% 5.44/2.10  tff(c_474, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_50, c_269, c_457])).
% 5.44/2.10  tff(c_484, plain, (k1_relat_1('#skF_5')='#skF_2'), inference(splitLeft, [status(thm)], [c_474])).
% 5.44/2.10  tff(c_159, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_54, c_139])).
% 5.44/2.10  tff(c_58, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_120])).
% 5.44/2.10  tff(c_56, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_120])).
% 5.44/2.10  tff(c_268, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_54, c_246])).
% 5.44/2.10  tff(c_454, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_4')='#skF_2' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_54, c_447])).
% 5.44/2.10  tff(c_471, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_56, c_268, c_454])).
% 5.44/2.10  tff(c_478, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(splitLeft, [status(thm)], [c_471])).
% 5.44/2.10  tff(c_600, plain, (![A_118, B_119]: (r2_hidden('#skF_1'(A_118, B_119), k1_relat_1(A_118)) | B_119=A_118 | k1_relat_1(B_119)!=k1_relat_1(A_118) | ~v1_funct_1(B_119) | ~v1_relat_1(B_119) | ~v1_funct_1(A_118) | ~v1_relat_1(A_118))), inference(cnfTransformation, [status(thm)], [f_67])).
% 5.44/2.10  tff(c_608, plain, (![B_119]: (r2_hidden('#skF_1'('#skF_4', B_119), '#skF_2') | B_119='#skF_4' | k1_relat_1(B_119)!=k1_relat_1('#skF_4') | ~v1_funct_1(B_119) | ~v1_relat_1(B_119) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_478, c_600])).
% 5.44/2.10  tff(c_635, plain, (![B_126]: (r2_hidden('#skF_1'('#skF_4', B_126), '#skF_2') | B_126='#skF_4' | k1_relat_1(B_126)!='#skF_2' | ~v1_funct_1(B_126) | ~v1_relat_1(B_126))), inference(demodulation, [status(thm), theory('equality')], [c_159, c_58, c_478, c_608])).
% 5.44/2.10  tff(c_46, plain, (![E_34]: (k1_funct_1('#skF_5', E_34)=k1_funct_1('#skF_4', E_34) | ~r2_hidden(E_34, '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_120])).
% 5.44/2.10  tff(c_989, plain, (![B_155]: (k1_funct_1('#skF_5', '#skF_1'('#skF_4', B_155))=k1_funct_1('#skF_4', '#skF_1'('#skF_4', B_155)) | B_155='#skF_4' | k1_relat_1(B_155)!='#skF_2' | ~v1_funct_1(B_155) | ~v1_relat_1(B_155))), inference(resolution, [status(thm)], [c_635, c_46])).
% 5.44/2.10  tff(c_22, plain, (![B_15, A_11]: (k1_funct_1(B_15, '#skF_1'(A_11, B_15))!=k1_funct_1(A_11, '#skF_1'(A_11, B_15)) | B_15=A_11 | k1_relat_1(B_15)!=k1_relat_1(A_11) | ~v1_funct_1(B_15) | ~v1_relat_1(B_15) | ~v1_funct_1(A_11) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_67])).
% 5.44/2.10  tff(c_996, plain, (k1_relat_1('#skF_5')!=k1_relat_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4') | '#skF_5'='#skF_4' | k1_relat_1('#skF_5')!='#skF_2' | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_989, c_22])).
% 5.44/2.10  tff(c_1003, plain, ('#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_160, c_52, c_484, c_159, c_58, c_484, c_478, c_996])).
% 5.44/2.10  tff(c_44, plain, (~r2_relset_1('#skF_2', '#skF_3', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_120])).
% 5.44/2.10  tff(c_1018, plain, (~r2_relset_1('#skF_2', '#skF_3', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1003, c_44])).
% 5.44/2.10  tff(c_1029, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_556, c_1018])).
% 5.44/2.10  tff(c_1030, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_474])).
% 5.44/2.10  tff(c_14, plain, (![A_5]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.44/2.10  tff(c_91, plain, (![A_42, B_43]: (r1_tarski(A_42, B_43) | ~m1_subset_1(A_42, k1_zfmisc_1(B_43)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.44/2.10  tff(c_107, plain, (![A_5]: (r1_tarski(k1_xboole_0, A_5))), inference(resolution, [status(thm)], [c_14, c_91])).
% 5.44/2.10  tff(c_1050, plain, (![A_5]: (r1_tarski('#skF_3', A_5))), inference(demodulation, [status(thm), theory('equality')], [c_1030, c_107])).
% 5.44/2.10  tff(c_10, plain, (![A_3]: (k2_zfmisc_1(A_3, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.44/2.10  tff(c_1053, plain, (![A_3]: (k2_zfmisc_1(A_3, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1030, c_1030, c_10])).
% 5.44/2.10  tff(c_105, plain, (r1_tarski('#skF_4', k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_54, c_91])).
% 5.44/2.10  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.44/2.10  tff(c_121, plain, (k2_zfmisc_1('#skF_2', '#skF_3')='#skF_4' | ~r1_tarski(k2_zfmisc_1('#skF_2', '#skF_3'), '#skF_4')), inference(resolution, [status(thm)], [c_105, c_2])).
% 5.44/2.10  tff(c_232, plain, (~r1_tarski(k2_zfmisc_1('#skF_2', '#skF_3'), '#skF_4')), inference(splitLeft, [status(thm)], [c_121])).
% 5.44/2.10  tff(c_1153, plain, (~r1_tarski('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1053, c_232])).
% 5.44/2.10  tff(c_1161, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1050, c_1153])).
% 5.44/2.10  tff(c_1162, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_471])).
% 5.44/2.10  tff(c_1182, plain, (![A_5]: (r1_tarski('#skF_3', A_5))), inference(demodulation, [status(thm), theory('equality')], [c_1162, c_107])).
% 5.44/2.10  tff(c_1185, plain, (![A_3]: (k2_zfmisc_1(A_3, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1162, c_1162, c_10])).
% 5.44/2.10  tff(c_1285, plain, (~r1_tarski('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1185, c_232])).
% 5.44/2.10  tff(c_1293, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1182, c_1285])).
% 5.44/2.10  tff(c_1294, plain, (k2_zfmisc_1('#skF_2', '#skF_3')='#skF_4'), inference(splitRight, [status(thm)], [c_121])).
% 5.44/2.10  tff(c_1300, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_1294, c_48])).
% 5.44/2.10  tff(c_1395, plain, (![A_186, B_187, C_188]: (k1_relset_1(A_186, B_187, C_188)=k1_relat_1(C_188) | ~m1_subset_1(C_188, k1_zfmisc_1(k2_zfmisc_1(A_186, B_187))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 5.44/2.10  tff(c_1415, plain, (![C_189]: (k1_relset_1('#skF_2', '#skF_3', C_189)=k1_relat_1(C_189) | ~m1_subset_1(C_189, k1_zfmisc_1('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_1294, c_1395])).
% 5.44/2.10  tff(c_1430, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_1300, c_1415])).
% 5.44/2.10  tff(c_1489, plain, (![B_197, C_198, A_199]: (k1_xboole_0=B_197 | v1_funct_2(C_198, A_199, B_197) | k1_relset_1(A_199, B_197, C_198)!=A_199 | ~m1_subset_1(C_198, k1_zfmisc_1(k2_zfmisc_1(A_199, B_197))))), inference(cnfTransformation, [status(thm)], [f_99])).
% 5.44/2.10  tff(c_1492, plain, (![C_198]: (k1_xboole_0='#skF_3' | v1_funct_2(C_198, '#skF_2', '#skF_3') | k1_relset_1('#skF_2', '#skF_3', C_198)!='#skF_2' | ~m1_subset_1(C_198, k1_zfmisc_1('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_1294, c_1489])).
% 5.44/2.10  tff(c_1618, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_1492])).
% 5.44/2.10  tff(c_8, plain, (![B_4, A_3]: (k1_xboole_0=B_4 | k1_xboole_0=A_3 | k2_zfmisc_1(A_3, B_4)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.44/2.10  tff(c_1309, plain, (k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0!='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_1294, c_8])).
% 5.44/2.10  tff(c_1385, plain, (k1_xboole_0!='#skF_4'), inference(splitLeft, [status(thm)], [c_1309])).
% 5.44/2.10  tff(c_1631, plain, ('#skF_3'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1618, c_1385])).
% 5.44/2.10  tff(c_1711, plain, (![A_222]: (k2_zfmisc_1(A_222, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1618, c_1618, c_10])).
% 5.44/2.10  tff(c_1730, plain, ('#skF_3'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_1711, c_1294])).
% 5.44/2.10  tff(c_1749, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1631, c_1730])).
% 5.44/2.10  tff(c_1751, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_1492])).
% 5.44/2.10  tff(c_1828, plain, (![B_230, A_231, C_232]: (k1_xboole_0=B_230 | k1_relset_1(A_231, B_230, C_232)=A_231 | ~v1_funct_2(C_232, A_231, B_230) | ~m1_subset_1(C_232, k1_zfmisc_1(k2_zfmisc_1(A_231, B_230))))), inference(cnfTransformation, [status(thm)], [f_99])).
% 5.44/2.10  tff(c_1831, plain, (![C_232]: (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', C_232)='#skF_2' | ~v1_funct_2(C_232, '#skF_2', '#skF_3') | ~m1_subset_1(C_232, k1_zfmisc_1('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_1294, c_1828])).
% 5.44/2.10  tff(c_1994, plain, (![C_261]: (k1_relset_1('#skF_2', '#skF_3', C_261)='#skF_2' | ~v1_funct_2(C_261, '#skF_2', '#skF_3') | ~m1_subset_1(C_261, k1_zfmisc_1('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_1751, c_1831])).
% 5.44/2.10  tff(c_1997, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_2' | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_1300, c_1994])).
% 5.44/2.10  tff(c_2011, plain, (k1_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_50, c_1430, c_1997])).
% 5.44/2.10  tff(c_1299, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_1294, c_54])).
% 5.44/2.10  tff(c_1431, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_1299, c_1415])).
% 5.44/2.10  tff(c_2000, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')='#skF_2' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_1299, c_1994])).
% 5.44/2.10  tff(c_2014, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_56, c_1431, c_2000])).
% 5.44/2.10  tff(c_24, plain, (![A_11, B_15]: (r2_hidden('#skF_1'(A_11, B_15), k1_relat_1(A_11)) | B_15=A_11 | k1_relat_1(B_15)!=k1_relat_1(A_11) | ~v1_funct_1(B_15) | ~v1_relat_1(B_15) | ~v1_funct_1(A_11) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_67])).
% 5.44/2.10  tff(c_2039, plain, (![B_15]: (r2_hidden('#skF_1'('#skF_4', B_15), '#skF_2') | B_15='#skF_4' | k1_relat_1(B_15)!=k1_relat_1('#skF_4') | ~v1_funct_1(B_15) | ~v1_relat_1(B_15) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_2014, c_24])).
% 5.44/2.10  tff(c_2097, plain, (![B_265]: (r2_hidden('#skF_1'('#skF_4', B_265), '#skF_2') | B_265='#skF_4' | k1_relat_1(B_265)!='#skF_2' | ~v1_funct_1(B_265) | ~v1_relat_1(B_265))), inference(demodulation, [status(thm), theory('equality')], [c_159, c_58, c_2014, c_2039])).
% 5.44/2.10  tff(c_2473, plain, (![B_285]: (k1_funct_1('#skF_5', '#skF_1'('#skF_4', B_285))=k1_funct_1('#skF_4', '#skF_1'('#skF_4', B_285)) | B_285='#skF_4' | k1_relat_1(B_285)!='#skF_2' | ~v1_funct_1(B_285) | ~v1_relat_1(B_285))), inference(resolution, [status(thm)], [c_2097, c_46])).
% 5.44/2.10  tff(c_2480, plain, (k1_relat_1('#skF_5')!=k1_relat_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4') | '#skF_5'='#skF_4' | k1_relat_1('#skF_5')!='#skF_2' | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_2473, c_22])).
% 5.44/2.10  tff(c_2487, plain, ('#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_160, c_52, c_2011, c_159, c_58, c_2014, c_2011, c_2480])).
% 5.44/2.10  tff(c_106, plain, (r1_tarski('#skF_5', k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_48, c_91])).
% 5.44/2.10  tff(c_124, plain, (k2_zfmisc_1('#skF_2', '#skF_3')='#skF_5' | ~r1_tarski(k2_zfmisc_1('#skF_2', '#skF_3'), '#skF_5')), inference(resolution, [status(thm)], [c_106, c_2])).
% 5.44/2.10  tff(c_224, plain, (~r1_tarski(k2_zfmisc_1('#skF_2', '#skF_3'), '#skF_5')), inference(splitLeft, [status(thm)], [c_124])).
% 5.44/2.10  tff(c_1296, plain, (~r1_tarski('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1294, c_224])).
% 5.44/2.10  tff(c_2498, plain, (~r1_tarski('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2487, c_1296])).
% 5.44/2.10  tff(c_2511, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_2498])).
% 5.44/2.10  tff(c_2513, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_1309])).
% 5.44/2.10  tff(c_2520, plain, (![A_5]: (r1_tarski('#skF_4', A_5))), inference(demodulation, [status(thm), theory('equality')], [c_2513, c_107])).
% 5.44/2.10  tff(c_2532, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2520, c_1296])).
% 5.44/2.10  tff(c_2533, plain, (k2_zfmisc_1('#skF_2', '#skF_3')='#skF_5'), inference(splitRight, [status(thm)], [c_124])).
% 5.44/2.10  tff(c_2545, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_2533, c_48])).
% 5.44/2.10  tff(c_2609, plain, (![A_295, B_296, C_297]: (k1_relset_1(A_295, B_296, C_297)=k1_relat_1(C_297) | ~m1_subset_1(C_297, k1_zfmisc_1(k2_zfmisc_1(A_295, B_296))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 5.44/2.10  tff(c_2711, plain, (![C_315]: (k1_relset_1('#skF_2', '#skF_3', C_315)=k1_relat_1(C_315) | ~m1_subset_1(C_315, k1_zfmisc_1('#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_2533, c_2609])).
% 5.44/2.10  tff(c_2727, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_2545, c_2711])).
% 5.44/2.10  tff(c_2826, plain, (![B_328, A_329, C_330]: (k1_xboole_0=B_328 | k1_relset_1(A_329, B_328, C_330)=A_329 | ~v1_funct_2(C_330, A_329, B_328) | ~m1_subset_1(C_330, k1_zfmisc_1(k2_zfmisc_1(A_329, B_328))))), inference(cnfTransformation, [status(thm)], [f_99])).
% 5.44/2.10  tff(c_2829, plain, (![C_330]: (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', C_330)='#skF_2' | ~v1_funct_2(C_330, '#skF_2', '#skF_3') | ~m1_subset_1(C_330, k1_zfmisc_1('#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_2533, c_2826])).
% 5.44/2.10  tff(c_2862, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_2829])).
% 5.44/2.10  tff(c_2554, plain, (k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0!='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_2533, c_8])).
% 5.44/2.10  tff(c_2637, plain, (k1_xboole_0!='#skF_5'), inference(splitLeft, [status(thm)], [c_2554])).
% 5.44/2.10  tff(c_2874, plain, ('#skF_5'!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_2862, c_2637])).
% 5.44/2.10  tff(c_2885, plain, (![A_3]: (k2_zfmisc_1(A_3, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2862, c_2862, c_10])).
% 5.44/2.10  tff(c_2968, plain, ('#skF_5'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_2885, c_2533])).
% 5.44/2.10  tff(c_2970, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2874, c_2968])).
% 5.44/2.10  tff(c_2973, plain, (![C_338]: (k1_relset_1('#skF_2', '#skF_3', C_338)='#skF_2' | ~v1_funct_2(C_338, '#skF_2', '#skF_3') | ~m1_subset_1(C_338, k1_zfmisc_1('#skF_5')))), inference(splitRight, [status(thm)], [c_2829])).
% 5.44/2.10  tff(c_2979, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_2' | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_2545, c_2973])).
% 5.44/2.10  tff(c_2993, plain, (k1_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_50, c_2727, c_2979])).
% 5.44/2.10  tff(c_2544, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_2533, c_54])).
% 5.44/2.10  tff(c_2726, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_2544, c_2711])).
% 5.44/2.10  tff(c_2976, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')='#skF_2' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_2544, c_2973])).
% 5.44/2.10  tff(c_2990, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_56, c_2726, c_2976])).
% 5.44/2.10  tff(c_3200, plain, (![A_364, B_365]: (r2_hidden('#skF_1'(A_364, B_365), k1_relat_1(A_364)) | B_365=A_364 | k1_relat_1(B_365)!=k1_relat_1(A_364) | ~v1_funct_1(B_365) | ~v1_relat_1(B_365) | ~v1_funct_1(A_364) | ~v1_relat_1(A_364))), inference(cnfTransformation, [status(thm)], [f_67])).
% 5.44/2.10  tff(c_3208, plain, (![B_365]: (r2_hidden('#skF_1'('#skF_4', B_365), '#skF_2') | B_365='#skF_4' | k1_relat_1(B_365)!=k1_relat_1('#skF_4') | ~v1_funct_1(B_365) | ~v1_relat_1(B_365) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_2990, c_3200])).
% 5.44/2.10  tff(c_3256, plain, (![B_373]: (r2_hidden('#skF_1'('#skF_4', B_373), '#skF_2') | B_373='#skF_4' | k1_relat_1(B_373)!='#skF_2' | ~v1_funct_1(B_373) | ~v1_relat_1(B_373))), inference(demodulation, [status(thm), theory('equality')], [c_159, c_58, c_2990, c_3208])).
% 5.44/2.10  tff(c_3643, plain, (![B_398]: (k1_funct_1('#skF_5', '#skF_1'('#skF_4', B_398))=k1_funct_1('#skF_4', '#skF_1'('#skF_4', B_398)) | B_398='#skF_4' | k1_relat_1(B_398)!='#skF_2' | ~v1_funct_1(B_398) | ~v1_relat_1(B_398))), inference(resolution, [status(thm)], [c_3256, c_46])).
% 5.44/2.10  tff(c_3650, plain, (k1_relat_1('#skF_5')!=k1_relat_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4') | '#skF_5'='#skF_4' | k1_relat_1('#skF_5')!='#skF_2' | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_3643, c_22])).
% 5.44/2.10  tff(c_3657, plain, ('#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_160, c_52, c_2993, c_159, c_58, c_2993, c_2990, c_3650])).
% 5.44/2.10  tff(c_2543, plain, (r1_tarski('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_2533, c_105])).
% 5.44/2.10  tff(c_2570, plain, ('#skF_5'='#skF_4' | ~r1_tarski('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_2543, c_2])).
% 5.44/2.10  tff(c_2607, plain, (~r1_tarski('#skF_5', '#skF_4')), inference(splitLeft, [status(thm)], [c_2570])).
% 5.44/2.10  tff(c_3678, plain, (~r1_tarski('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_3657, c_2607])).
% 5.44/2.10  tff(c_3695, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_3678])).
% 5.44/2.10  tff(c_3697, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_2554])).
% 5.44/2.10  tff(c_3705, plain, (![A_5]: (r1_tarski('#skF_5', A_5))), inference(demodulation, [status(thm), theory('equality')], [c_3697, c_107])).
% 5.44/2.10  tff(c_3717, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3705, c_2607])).
% 5.44/2.10  tff(c_3718, plain, ('#skF_5'='#skF_4'), inference(splitRight, [status(thm)], [c_2570])).
% 5.44/2.10  tff(c_3728, plain, (~r2_relset_1('#skF_2', '#skF_3', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_3718, c_44])).
% 5.44/2.10  tff(c_3722, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_3718, c_2544])).
% 5.44/2.10  tff(c_3725, plain, (k2_zfmisc_1('#skF_2', '#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_3718, c_2533])).
% 5.44/2.10  tff(c_4170, plain, (![A_448, B_449, C_450, D_451]: (r2_relset_1(A_448, B_449, C_450, C_450) | ~m1_subset_1(D_451, k1_zfmisc_1(k2_zfmisc_1(A_448, B_449))) | ~m1_subset_1(C_450, k1_zfmisc_1(k2_zfmisc_1(A_448, B_449))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 5.44/2.10  tff(c_4187, plain, (![A_452, B_453, C_454]: (r2_relset_1(A_452, B_453, C_454, C_454) | ~m1_subset_1(C_454, k1_zfmisc_1(k2_zfmisc_1(A_452, B_453))))), inference(resolution, [status(thm)], [c_14, c_4170])).
% 5.44/2.10  tff(c_4213, plain, (![C_459]: (r2_relset_1('#skF_2', '#skF_3', C_459, C_459) | ~m1_subset_1(C_459, k1_zfmisc_1('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_3725, c_4187])).
% 5.44/2.10  tff(c_4215, plain, (r2_relset_1('#skF_2', '#skF_3', '#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_3722, c_4213])).
% 5.44/2.10  tff(c_4225, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3728, c_4215])).
% 5.44/2.10  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.44/2.10  
% 5.44/2.10  Inference rules
% 5.44/2.10  ----------------------
% 5.44/2.10  #Ref     : 3
% 5.44/2.10  #Sup     : 847
% 5.44/2.10  #Fact    : 0
% 5.44/2.10  #Define  : 0
% 5.44/2.10  #Split   : 23
% 5.44/2.10  #Chain   : 0
% 5.44/2.10  #Close   : 0
% 5.44/2.10  
% 5.44/2.10  Ordering : KBO
% 5.44/2.10  
% 5.44/2.10  Simplification rules
% 5.44/2.10  ----------------------
% 5.44/2.10  #Subsume      : 139
% 5.44/2.10  #Demod        : 949
% 5.44/2.10  #Tautology    : 376
% 5.44/2.10  #SimpNegUnit  : 51
% 5.44/2.10  #BackRed      : 241
% 5.44/2.10  
% 5.44/2.10  #Partial instantiations: 0
% 5.44/2.10  #Strategies tried      : 1
% 5.44/2.10  
% 5.44/2.10  Timing (in seconds)
% 5.44/2.10  ----------------------
% 5.44/2.10  Preprocessing        : 0.34
% 5.44/2.10  Parsing              : 0.18
% 5.44/2.10  CNF conversion       : 0.02
% 5.44/2.10  Main loop            : 0.89
% 5.44/2.10  Inferencing          : 0.30
% 5.44/2.10  Reduction            : 0.29
% 5.44/2.10  Demodulation         : 0.20
% 5.44/2.10  BG Simplification    : 0.04
% 5.44/2.10  Subsumption          : 0.17
% 5.44/2.10  Abstraction          : 0.05
% 5.44/2.10  MUC search           : 0.00
% 5.44/2.10  Cooper               : 0.00
% 5.44/2.10  Total                : 1.27
% 5.44/2.10  Index Insertion      : 0.00
% 5.44/2.10  Index Deletion       : 0.00
% 5.44/2.10  Index Matching       : 0.00
% 5.44/2.10  BG Taut test         : 0.00
%------------------------------------------------------------------------------
