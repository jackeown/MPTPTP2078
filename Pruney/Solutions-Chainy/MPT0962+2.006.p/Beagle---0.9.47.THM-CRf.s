%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:52 EST 2020

% Result     : Theorem 6.38s
% Output     : CNFRefutation 6.66s
% Verified   : 
% Statistics : Number of formulae       :  224 (2483 expanded)
%              Number of leaves         :   33 ( 779 expanded)
%              Depth                    :   15
%              Number of atoms          :  444 (6234 expanded)
%              Number of equality atoms :  103 (1093 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k3_mcart_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff(k3_mcart_1,type,(
    k3_mcart_1: ( $i * $i * $i ) > $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_126,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => ( r1_tarski(k2_relat_1(B),A)
         => ( v1_funct_1(B)
            & v1_funct_2(B,k1_relat_1(B),A)
            & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B),A))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).

tff(f_32,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_79,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

tff(f_95,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D,E] :
                  ~ ( ( r2_hidden(C,A)
                      | r2_hidden(D,A) )
                    & B = k3_mcart_1(C,D,E) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_mcart_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_64,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(A,B)
           => ( r1_tarski(k1_relat_1(A),k1_relat_1(B))
              & r1_tarski(k2_relat_1(A),k2_relat_1(B)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relat_1)).

tff(f_113,axiom,(
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

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_53,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_67,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(c_60,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_8,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_56,plain,(
    r1_tarski(k2_relat_1('#skF_3'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_6601,plain,(
    ! [C_716,A_717,B_718] :
      ( m1_subset_1(C_716,k1_zfmisc_1(k2_zfmisc_1(A_717,B_718)))
      | ~ r1_tarski(k2_relat_1(C_716),B_718)
      | ~ r1_tarski(k1_relat_1(C_716),A_717)
      | ~ v1_relat_1(C_716) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_58,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_54,plain,
    ( ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2')))
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),'#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_62,plain,
    ( ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2')))
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_54])).

tff(c_99,plain,(
    ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_62])).

tff(c_36,plain,(
    ! [A_20] :
      ( r2_hidden('#skF_1'(A_20),A_20)
      | k1_xboole_0 = A_20 ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_18,plain,(
    ! [A_5,B_6] :
      ( m1_subset_1(A_5,k1_zfmisc_1(B_6))
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_134,plain,(
    ! [C_50,B_51,A_52] :
      ( ~ v1_xboole_0(C_50)
      | ~ m1_subset_1(B_51,k1_zfmisc_1(C_50))
      | ~ r2_hidden(A_52,B_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_138,plain,(
    ! [B_53,A_54,A_55] :
      ( ~ v1_xboole_0(B_53)
      | ~ r2_hidden(A_54,A_55)
      | ~ r1_tarski(A_55,B_53) ) ),
    inference(resolution,[status(thm)],[c_18,c_134])).

tff(c_142,plain,(
    ! [B_56,A_57] :
      ( ~ v1_xboole_0(B_56)
      | ~ r1_tarski(A_57,B_56)
      | k1_xboole_0 = A_57 ) ),
    inference(resolution,[status(thm)],[c_36,c_138])).

tff(c_149,plain,
    ( ~ v1_xboole_0('#skF_2')
    | k2_relat_1('#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_56,c_142])).

tff(c_157,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_149])).

tff(c_26,plain,(
    ! [A_11,B_13] :
      ( r1_tarski(k1_relat_1(A_11),k1_relat_1(B_13))
      | ~ r1_tarski(A_11,B_13)
      | ~ v1_relat_1(B_13)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_468,plain,(
    ! [C_111,A_112,B_113] :
      ( m1_subset_1(C_111,k1_zfmisc_1(k2_zfmisc_1(A_112,B_113)))
      | ~ r1_tarski(k2_relat_1(C_111),B_113)
      | ~ r1_tarski(k1_relat_1(C_111),A_112)
      | ~ v1_relat_1(C_111) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_16,plain,(
    ! [A_5,B_6] :
      ( r1_tarski(A_5,B_6)
      | ~ m1_subset_1(A_5,k1_zfmisc_1(B_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_705,plain,(
    ! [C_144,A_145,B_146] :
      ( r1_tarski(C_144,k2_zfmisc_1(A_145,B_146))
      | ~ r1_tarski(k2_relat_1(C_144),B_146)
      | ~ r1_tarski(k1_relat_1(C_144),A_145)
      | ~ v1_relat_1(C_144) ) ),
    inference(resolution,[status(thm)],[c_468,c_16])).

tff(c_711,plain,(
    ! [A_145] :
      ( r1_tarski('#skF_3',k2_zfmisc_1(A_145,'#skF_2'))
      | ~ r1_tarski(k1_relat_1('#skF_3'),A_145)
      | ~ v1_relat_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_56,c_705])).

tff(c_726,plain,(
    ! [A_147] :
      ( r1_tarski('#skF_3',k2_zfmisc_1(A_147,'#skF_2'))
      | ~ r1_tarski(k1_relat_1('#skF_3'),A_147) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_711])).

tff(c_734,plain,(
    ! [B_13] :
      ( r1_tarski('#skF_3',k2_zfmisc_1(k1_relat_1(B_13),'#skF_2'))
      | ~ r1_tarski('#skF_3',B_13)
      | ~ v1_relat_1(B_13)
      | ~ v1_relat_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_26,c_726])).

tff(c_745,plain,(
    ! [B_13] :
      ( r1_tarski('#skF_3',k2_zfmisc_1(k1_relat_1(B_13),'#skF_2'))
      | ~ r1_tarski('#skF_3',B_13)
      | ~ v1_relat_1(B_13) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_734])).

tff(c_546,plain,(
    ! [B_125,A_126,C_127] :
      ( k1_xboole_0 = B_125
      | k1_relset_1(A_126,B_125,C_127) = A_126
      | ~ v1_funct_2(C_127,A_126,B_125)
      | ~ m1_subset_1(C_127,k1_zfmisc_1(k2_zfmisc_1(A_126,B_125))) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_1009,plain,(
    ! [B_168,A_169,A_170] :
      ( k1_xboole_0 = B_168
      | k1_relset_1(A_169,B_168,A_170) = A_169
      | ~ v1_funct_2(A_170,A_169,B_168)
      | ~ r1_tarski(A_170,k2_zfmisc_1(A_169,B_168)) ) ),
    inference(resolution,[status(thm)],[c_18,c_546])).

tff(c_1033,plain,(
    ! [B_13] :
      ( k1_xboole_0 = '#skF_2'
      | k1_relset_1(k1_relat_1(B_13),'#skF_2','#skF_3') = k1_relat_1(B_13)
      | ~ v1_funct_2('#skF_3',k1_relat_1(B_13),'#skF_2')
      | ~ r1_tarski('#skF_3',B_13)
      | ~ v1_relat_1(B_13) ) ),
    inference(resolution,[status(thm)],[c_745,c_1009])).

tff(c_1381,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_1033])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_1445,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1381,c_2])).

tff(c_1447,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_157,c_1445])).

tff(c_1449,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_1033])).

tff(c_746,plain,(
    r1_tarski('#skF_3',k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2')) ),
    inference(resolution,[status(thm)],[c_8,c_726])).

tff(c_243,plain,(
    ! [A_79,B_80,C_81] :
      ( k1_relset_1(A_79,B_80,C_81) = k1_relat_1(C_81)
      | ~ m1_subset_1(C_81,k1_zfmisc_1(k2_zfmisc_1(A_79,B_80))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_254,plain,(
    ! [A_79,B_80,A_5] :
      ( k1_relset_1(A_79,B_80,A_5) = k1_relat_1(A_5)
      | ~ r1_tarski(A_5,k2_zfmisc_1(A_79,B_80)) ) ),
    inference(resolution,[status(thm)],[c_18,c_243])).

tff(c_755,plain,(
    k1_relset_1(k1_relat_1('#skF_3'),'#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_746,c_254])).

tff(c_647,plain,(
    ! [B_138,C_139,A_140] :
      ( k1_xboole_0 = B_138
      | v1_funct_2(C_139,A_140,B_138)
      | k1_relset_1(A_140,B_138,C_139) != A_140
      | ~ m1_subset_1(C_139,k1_zfmisc_1(k2_zfmisc_1(A_140,B_138))) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_1450,plain,(
    ! [B_193,A_194,A_195] :
      ( k1_xboole_0 = B_193
      | v1_funct_2(A_194,A_195,B_193)
      | k1_relset_1(A_195,B_193,A_194) != A_195
      | ~ r1_tarski(A_194,k2_zfmisc_1(A_195,B_193)) ) ),
    inference(resolution,[status(thm)],[c_18,c_647])).

tff(c_1462,plain,
    ( k1_xboole_0 = '#skF_2'
    | v1_funct_2('#skF_3',k1_relat_1('#skF_3'),'#skF_2')
    | k1_relset_1(k1_relat_1('#skF_3'),'#skF_2','#skF_3') != k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_746,c_1450])).

tff(c_1480,plain,
    ( k1_xboole_0 = '#skF_2'
    | v1_funct_2('#skF_3',k1_relat_1('#skF_3'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_755,c_1462])).

tff(c_1482,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_99,c_1449,c_1480])).

tff(c_1484,plain,(
    v1_xboole_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_149])).

tff(c_150,plain,(
    ! [B_2] :
      ( ~ v1_xboole_0(B_2)
      | k1_xboole_0 = B_2 ) ),
    inference(resolution,[status(thm)],[c_8,c_142])).

tff(c_1491,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_1484,c_150])).

tff(c_1483,plain,(
    k2_relat_1('#skF_3') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_149])).

tff(c_1511,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1491,c_1483])).

tff(c_123,plain,(
    ! [B_48,A_49] :
      ( B_48 = A_49
      | ~ r1_tarski(B_48,A_49)
      | ~ r1_tarski(A_49,B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_128,plain,
    ( k2_relat_1('#skF_3') = '#skF_2'
    | ~ r1_tarski('#skF_2',k2_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_56,c_123])).

tff(c_133,plain,(
    ~ r1_tarski('#skF_2',k2_relat_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_128])).

tff(c_1512,plain,(
    ~ r1_tarski('#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1511,c_133])).

tff(c_1516,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_1512])).

tff(c_1517,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_128])).

tff(c_4222,plain,(
    ! [C_470,A_471,B_472] :
      ( m1_subset_1(C_470,k1_zfmisc_1(k2_zfmisc_1(A_471,B_472)))
      | ~ r1_tarski(k2_relat_1(C_470),B_472)
      | ~ r1_tarski(k1_relat_1(C_470),A_471)
      | ~ v1_relat_1(C_470) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_4516,plain,(
    ! [C_504,A_505,B_506] :
      ( r1_tarski(C_504,k2_zfmisc_1(A_505,B_506))
      | ~ r1_tarski(k2_relat_1(C_504),B_506)
      | ~ r1_tarski(k1_relat_1(C_504),A_505)
      | ~ v1_relat_1(C_504) ) ),
    inference(resolution,[status(thm)],[c_4222,c_16])).

tff(c_4982,plain,(
    ! [C_536,A_537] :
      ( r1_tarski(C_536,k2_zfmisc_1(A_537,k2_relat_1(C_536)))
      | ~ r1_tarski(k1_relat_1(C_536),A_537)
      | ~ v1_relat_1(C_536) ) ),
    inference(resolution,[status(thm)],[c_8,c_4516])).

tff(c_5020,plain,(
    ! [A_537] :
      ( r1_tarski('#skF_3',k2_zfmisc_1(A_537,'#skF_2'))
      | ~ r1_tarski(k1_relat_1('#skF_3'),A_537)
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1517,c_4982])).

tff(c_5059,plain,(
    ! [A_539] :
      ( r1_tarski('#skF_3',k2_zfmisc_1(A_539,'#skF_2'))
      | ~ r1_tarski(k1_relat_1('#skF_3'),A_539) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_5020])).

tff(c_5089,plain,(
    r1_tarski('#skF_3',k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2')) ),
    inference(resolution,[status(thm)],[c_8,c_5059])).

tff(c_3941,plain,(
    ! [A_438,B_439,C_440] :
      ( k1_relset_1(A_438,B_439,C_440) = k1_relat_1(C_440)
      | ~ m1_subset_1(C_440,k1_zfmisc_1(k2_zfmisc_1(A_438,B_439))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_3952,plain,(
    ! [A_438,B_439,A_5] :
      ( k1_relset_1(A_438,B_439,A_5) = k1_relat_1(A_5)
      | ~ r1_tarski(A_5,k2_zfmisc_1(A_438,B_439)) ) ),
    inference(resolution,[status(thm)],[c_18,c_3941])).

tff(c_5118,plain,(
    k1_relset_1(k1_relat_1('#skF_3'),'#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_5089,c_3952])).

tff(c_4320,plain,(
    ! [B_480,C_481,A_482] :
      ( k1_xboole_0 = B_480
      | v1_funct_2(C_481,A_482,B_480)
      | k1_relset_1(A_482,B_480,C_481) != A_482
      | ~ m1_subset_1(C_481,k1_zfmisc_1(k2_zfmisc_1(A_482,B_480))) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_5169,plain,(
    ! [B_543,A_544,A_545] :
      ( k1_xboole_0 = B_543
      | v1_funct_2(A_544,A_545,B_543)
      | k1_relset_1(A_545,B_543,A_544) != A_545
      | ~ r1_tarski(A_544,k2_zfmisc_1(A_545,B_543)) ) ),
    inference(resolution,[status(thm)],[c_18,c_4320])).

tff(c_5172,plain,
    ( k1_xboole_0 = '#skF_2'
    | v1_funct_2('#skF_3',k1_relat_1('#skF_3'),'#skF_2')
    | k1_relset_1(k1_relat_1('#skF_3'),'#skF_2','#skF_3') != k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_5089,c_5169])).

tff(c_5200,plain,
    ( k1_xboole_0 = '#skF_2'
    | v1_funct_2('#skF_3',k1_relat_1('#skF_3'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5118,c_5172])).

tff(c_5201,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_99,c_5200])).

tff(c_1649,plain,(
    ! [A_228,B_229] :
      ( r1_tarski(k2_relat_1(A_228),k2_relat_1(B_229))
      | ~ r1_tarski(A_228,B_229)
      | ~ v1_relat_1(B_229)
      | ~ v1_relat_1(A_228) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_1660,plain,(
    ! [A_228] :
      ( r1_tarski(k2_relat_1(A_228),'#skF_2')
      | ~ r1_tarski(A_228,'#skF_3')
      | ~ v1_relat_1('#skF_3')
      | ~ v1_relat_1(A_228) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1517,c_1649])).

tff(c_1750,plain,(
    ! [A_236] :
      ( r1_tarski(k2_relat_1(A_236),'#skF_2')
      | ~ r1_tarski(A_236,'#skF_3')
      | ~ v1_relat_1(A_236) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_1660])).

tff(c_1526,plain,(
    ! [C_196,B_197,A_198] :
      ( ~ v1_xboole_0(C_196)
      | ~ m1_subset_1(B_197,k1_zfmisc_1(C_196))
      | ~ r2_hidden(A_198,B_197) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1530,plain,(
    ! [B_199,A_200,A_201] :
      ( ~ v1_xboole_0(B_199)
      | ~ r2_hidden(A_200,A_201)
      | ~ r1_tarski(A_201,B_199) ) ),
    inference(resolution,[status(thm)],[c_18,c_1526])).

tff(c_1533,plain,(
    ! [B_199,A_20] :
      ( ~ v1_xboole_0(B_199)
      | ~ r1_tarski(A_20,B_199)
      | k1_xboole_0 = A_20 ) ),
    inference(resolution,[status(thm)],[c_36,c_1530])).

tff(c_1762,plain,(
    ! [A_236] :
      ( ~ v1_xboole_0('#skF_2')
      | k2_relat_1(A_236) = k1_xboole_0
      | ~ r1_tarski(A_236,'#skF_3')
      | ~ v1_relat_1(A_236) ) ),
    inference(resolution,[status(thm)],[c_1750,c_1533])).

tff(c_1868,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_1762])).

tff(c_2011,plain,(
    ! [C_268,A_269,B_270] :
      ( m1_subset_1(C_268,k1_zfmisc_1(k2_zfmisc_1(A_269,B_270)))
      | ~ r1_tarski(k2_relat_1(C_268),B_270)
      | ~ r1_tarski(k1_relat_1(C_268),A_269)
      | ~ v1_relat_1(C_268) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_2237,plain,(
    ! [C_296,A_297,B_298] :
      ( r1_tarski(C_296,k2_zfmisc_1(A_297,B_298))
      | ~ r1_tarski(k2_relat_1(C_296),B_298)
      | ~ r1_tarski(k1_relat_1(C_296),A_297)
      | ~ v1_relat_1(C_296) ) ),
    inference(resolution,[status(thm)],[c_2011,c_16])).

tff(c_2332,plain,(
    ! [C_305,A_306] :
      ( r1_tarski(C_305,k2_zfmisc_1(A_306,k2_relat_1(C_305)))
      | ~ r1_tarski(k1_relat_1(C_305),A_306)
      | ~ v1_relat_1(C_305) ) ),
    inference(resolution,[status(thm)],[c_8,c_2237])).

tff(c_2349,plain,(
    ! [A_306] :
      ( r1_tarski('#skF_3',k2_zfmisc_1(A_306,'#skF_2'))
      | ~ r1_tarski(k1_relat_1('#skF_3'),A_306)
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1517,c_2332])).

tff(c_2368,plain,(
    ! [A_307] :
      ( r1_tarski('#skF_3',k2_zfmisc_1(A_307,'#skF_2'))
      | ~ r1_tarski(k1_relat_1('#skF_3'),A_307) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_2349])).

tff(c_2393,plain,(
    r1_tarski('#skF_3',k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2')) ),
    inference(resolution,[status(thm)],[c_8,c_2368])).

tff(c_1722,plain,(
    ! [A_232,B_233,C_234] :
      ( k1_relset_1(A_232,B_233,C_234) = k1_relat_1(C_234)
      | ~ m1_subset_1(C_234,k1_zfmisc_1(k2_zfmisc_1(A_232,B_233))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_1733,plain,(
    ! [A_232,B_233,A_5] :
      ( k1_relset_1(A_232,B_233,A_5) = k1_relat_1(A_5)
      | ~ r1_tarski(A_5,k2_zfmisc_1(A_232,B_233)) ) ),
    inference(resolution,[status(thm)],[c_18,c_1722])).

tff(c_2402,plain,(
    k1_relset_1(k1_relat_1('#skF_3'),'#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_2393,c_1733])).

tff(c_2051,plain,(
    ! [B_275,C_276,A_277] :
      ( k1_xboole_0 = B_275
      | v1_funct_2(C_276,A_277,B_275)
      | k1_relset_1(A_277,B_275,C_276) != A_277
      | ~ m1_subset_1(C_276,k1_zfmisc_1(k2_zfmisc_1(A_277,B_275))) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_2420,plain,(
    ! [B_309,A_310,A_311] :
      ( k1_xboole_0 = B_309
      | v1_funct_2(A_310,A_311,B_309)
      | k1_relset_1(A_311,B_309,A_310) != A_311
      | ~ r1_tarski(A_310,k2_zfmisc_1(A_311,B_309)) ) ),
    inference(resolution,[status(thm)],[c_18,c_2051])).

tff(c_2423,plain,
    ( k1_xboole_0 = '#skF_2'
    | v1_funct_2('#skF_3',k1_relat_1('#skF_3'),'#skF_2')
    | k1_relset_1(k1_relat_1('#skF_3'),'#skF_2','#skF_3') != k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_2393,c_2420])).

tff(c_2442,plain,
    ( k1_xboole_0 = '#skF_2'
    | v1_funct_2('#skF_3',k1_relat_1('#skF_3'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2402,c_2423])).

tff(c_2443,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_99,c_2442])).

tff(c_12,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2224,plain,(
    ! [C_294,A_295] :
      ( m1_subset_1(C_294,k1_zfmisc_1(k1_xboole_0))
      | ~ r1_tarski(k2_relat_1(C_294),k1_xboole_0)
      | ~ r1_tarski(k1_relat_1(C_294),A_295)
      | ~ v1_relat_1(C_294) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_2011])).

tff(c_2228,plain,(
    ! [A_295] :
      ( m1_subset_1('#skF_3',k1_zfmisc_1(k1_xboole_0))
      | ~ r1_tarski('#skF_2',k1_xboole_0)
      | ~ r1_tarski(k1_relat_1('#skF_3'),A_295)
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1517,c_2224])).

tff(c_2233,plain,(
    ! [A_295] :
      ( m1_subset_1('#skF_3',k1_zfmisc_1(k1_xboole_0))
      | ~ r1_tarski('#skF_2',k1_xboole_0)
      | ~ r1_tarski(k1_relat_1('#skF_3'),A_295) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_2228])).

tff(c_2236,plain,(
    ~ r1_tarski('#skF_2',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_2233])).

tff(c_2453,plain,(
    ~ r1_tarski('#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2443,c_2236])).

tff(c_2509,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_2453])).

tff(c_2511,plain,(
    r1_tarski('#skF_2',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_2233])).

tff(c_2524,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_2511,c_1533])).

tff(c_2533,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_2524])).

tff(c_2588,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2533,c_2])).

tff(c_2591,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1868,c_2588])).

tff(c_2593,plain,(
    v1_xboole_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_1762])).

tff(c_1657,plain,(
    ! [B_229] :
      ( r1_tarski('#skF_2',k2_relat_1(B_229))
      | ~ r1_tarski('#skF_3',B_229)
      | ~ v1_relat_1(B_229)
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1517,c_1649])).

tff(c_1768,plain,(
    ! [B_237] :
      ( r1_tarski('#skF_2',k2_relat_1(B_237))
      | ~ r1_tarski('#skF_3',B_237)
      | ~ v1_relat_1(B_237) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_1657])).

tff(c_1780,plain,(
    ! [B_237] :
      ( ~ v1_xboole_0(k2_relat_1(B_237))
      | k1_xboole_0 = '#skF_2'
      | ~ r1_tarski('#skF_3',B_237)
      | ~ v1_relat_1(B_237) ) ),
    inference(resolution,[status(thm)],[c_1768,c_1533])).

tff(c_2866,plain,(
    ! [B_334] :
      ( ~ v1_xboole_0(k2_relat_1(B_334))
      | ~ r1_tarski('#skF_3',B_334)
      | ~ v1_relat_1(B_334) ) ),
    inference(splitLeft,[status(thm)],[c_1780])).

tff(c_2872,plain,
    ( ~ v1_xboole_0('#skF_2')
    | ~ r1_tarski('#skF_3','#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1517,c_2866])).

tff(c_2877,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_8,c_2593,c_2872])).

tff(c_2878,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_1780])).

tff(c_100,plain,(
    ! [A_40] :
      ( v1_relat_1(A_40)
      | ~ v1_xboole_0(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_104,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_100])).

tff(c_28,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_1666,plain,(
    ! [A_228] :
      ( r1_tarski(k2_relat_1(A_228),k1_xboole_0)
      | ~ r1_tarski(A_228,k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_228) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_1649])).

tff(c_1697,plain,(
    ! [A_231] :
      ( r1_tarski(k2_relat_1(A_231),k1_xboole_0)
      | ~ r1_tarski(A_231,k1_xboole_0)
      | ~ v1_relat_1(A_231) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_1666])).

tff(c_1708,plain,
    ( r1_tarski('#skF_2',k1_xboole_0)
    | ~ r1_tarski('#skF_3',k1_xboole_0)
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1517,c_1697])).

tff(c_1718,plain,
    ( r1_tarski('#skF_2',k1_xboole_0)
    | ~ r1_tarski('#skF_3',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_1708])).

tff(c_1721,plain,(
    ~ r1_tarski('#skF_3',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_1718])).

tff(c_2911,plain,(
    ~ r1_tarski('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2878,c_1721])).

tff(c_2932,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2878,c_2878,c_12])).

tff(c_3034,plain,(
    ! [C_344,A_345,B_346] :
      ( m1_subset_1(C_344,k1_zfmisc_1(k2_zfmisc_1(A_345,B_346)))
      | ~ r1_tarski(k2_relat_1(C_344),B_346)
      | ~ r1_tarski(k1_relat_1(C_344),A_345)
      | ~ v1_relat_1(C_344) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_3551,plain,(
    ! [C_411,A_412,B_413] :
      ( r1_tarski(C_411,k2_zfmisc_1(A_412,B_413))
      | ~ r1_tarski(k2_relat_1(C_411),B_413)
      | ~ r1_tarski(k1_relat_1(C_411),A_412)
      | ~ v1_relat_1(C_411) ) ),
    inference(resolution,[status(thm)],[c_3034,c_16])).

tff(c_3617,plain,(
    ! [C_418,A_419] :
      ( r1_tarski(C_418,k2_zfmisc_1(A_419,k2_relat_1(C_418)))
      | ~ r1_tarski(k1_relat_1(C_418),A_419)
      | ~ v1_relat_1(C_418) ) ),
    inference(resolution,[status(thm)],[c_8,c_3551])).

tff(c_3641,plain,(
    ! [A_419] :
      ( r1_tarski('#skF_3',k2_zfmisc_1(A_419,'#skF_2'))
      | ~ r1_tarski(k1_relat_1('#skF_3'),A_419)
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1517,c_3617])).

tff(c_3652,plain,(
    ! [A_419] :
      ( r1_tarski('#skF_3','#skF_2')
      | ~ r1_tarski(k1_relat_1('#skF_3'),A_419) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_2932,c_3641])).

tff(c_3676,plain,(
    ! [A_422] : ~ r1_tarski(k1_relat_1('#skF_3'),A_422) ),
    inference(negUnitSimplification,[status(thm)],[c_2911,c_3652])).

tff(c_3700,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_8,c_3676])).

tff(c_3701,plain,(
    r1_tarski('#skF_2',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_1718])).

tff(c_3708,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_3701,c_1533])).

tff(c_3714,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_3708])).

tff(c_3740,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3714,c_2])).

tff(c_3702,plain,(
    r1_tarski('#skF_3',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_1718])).

tff(c_3757,plain,(
    r1_tarski('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3714,c_3702])).

tff(c_3886,plain,(
    ! [B_436,A_437] :
      ( ~ v1_xboole_0(B_436)
      | ~ r1_tarski(A_437,B_436)
      | A_437 = '#skF_2' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3714,c_1533])).

tff(c_3895,plain,
    ( ~ v1_xboole_0('#skF_2')
    | '#skF_2' = '#skF_3' ),
    inference(resolution,[status(thm)],[c_3757,c_3886])).

tff(c_3912,plain,(
    '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3740,c_3895])).

tff(c_1663,plain,(
    ! [B_229] :
      ( r1_tarski(k1_xboole_0,k2_relat_1(B_229))
      | ~ r1_tarski(k1_xboole_0,B_229)
      | ~ v1_relat_1(B_229)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_1649])).

tff(c_1677,plain,(
    ! [B_230] :
      ( r1_tarski(k1_xboole_0,k2_relat_1(B_230))
      | ~ r1_tarski(k1_xboole_0,B_230)
      | ~ v1_relat_1(B_230) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_1663])).

tff(c_1685,plain,
    ( r1_tarski(k1_xboole_0,'#skF_2')
    | ~ r1_tarski(k1_xboole_0,'#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1517,c_1677])).

tff(c_1693,plain,
    ( r1_tarski(k1_xboole_0,'#skF_2')
    | ~ r1_tarski(k1_xboole_0,'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_1685])).

tff(c_1696,plain,(
    ~ r1_tarski(k1_xboole_0,'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_1693])).

tff(c_3718,plain,(
    ~ r1_tarski('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3714,c_1696])).

tff(c_3925,plain,(
    ~ r1_tarski('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3912,c_3718])).

tff(c_3938,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_3925])).

tff(c_3939,plain,(
    r1_tarski(k1_xboole_0,'#skF_2') ),
    inference(splitRight,[status(thm)],[c_1693])).

tff(c_4,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_3960,plain,
    ( k1_xboole_0 = '#skF_2'
    | ~ r1_tarski('#skF_2',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_3939,c_4])).

tff(c_3969,plain,(
    ~ r1_tarski('#skF_2',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_3960])).

tff(c_5258,plain,(
    ~ r1_tarski('#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5201,c_3969])).

tff(c_5285,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_5258])).

tff(c_5286,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_3960])).

tff(c_3940,plain,(
    r1_tarski(k1_xboole_0,'#skF_3') ),
    inference(splitRight,[status(thm)],[c_1693])).

tff(c_3968,plain,
    ( k1_xboole_0 = '#skF_3'
    | ~ r1_tarski('#skF_3',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_3940,c_4])).

tff(c_5436,plain,
    ( '#skF_2' = '#skF_3'
    | ~ r1_tarski('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5286,c_5286,c_3968])).

tff(c_5437,plain,(
    ~ r1_tarski('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_5436])).

tff(c_5308,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5286,c_5286,c_12])).

tff(c_5568,plain,(
    ! [C_566,A_567,B_568] :
      ( m1_subset_1(C_566,k1_zfmisc_1(k2_zfmisc_1(A_567,B_568)))
      | ~ r1_tarski(k2_relat_1(C_566),B_568)
      | ~ r1_tarski(k1_relat_1(C_566),A_567)
      | ~ v1_relat_1(C_566) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_5830,plain,(
    ! [C_611,A_612,B_613] :
      ( r1_tarski(C_611,k2_zfmisc_1(A_612,B_613))
      | ~ r1_tarski(k2_relat_1(C_611),B_613)
      | ~ r1_tarski(k1_relat_1(C_611),A_612)
      | ~ v1_relat_1(C_611) ) ),
    inference(resolution,[status(thm)],[c_5568,c_16])).

tff(c_5840,plain,(
    ! [A_612,B_613] :
      ( r1_tarski('#skF_3',k2_zfmisc_1(A_612,B_613))
      | ~ r1_tarski('#skF_2',B_613)
      | ~ r1_tarski(k1_relat_1('#skF_3'),A_612)
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1517,c_5830])).

tff(c_5899,plain,(
    ! [A_618,B_619] :
      ( r1_tarski('#skF_3',k2_zfmisc_1(A_618,B_619))
      | ~ r1_tarski('#skF_2',B_619)
      | ~ r1_tarski(k1_relat_1('#skF_3'),A_618) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_5840])).

tff(c_5948,plain,(
    ! [B_621] :
      ( r1_tarski('#skF_3',k2_zfmisc_1(k1_relat_1('#skF_3'),B_621))
      | ~ r1_tarski('#skF_2',B_621) ) ),
    inference(resolution,[status(thm)],[c_8,c_5899])).

tff(c_5960,plain,
    ( r1_tarski('#skF_3','#skF_2')
    | ~ r1_tarski('#skF_2','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_5308,c_5948])).

tff(c_5965,plain,(
    r1_tarski('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_5960])).

tff(c_5967,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5437,c_5965])).

tff(c_5968,plain,(
    '#skF_2' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_5436])).

tff(c_30,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_5310,plain,(
    k1_relat_1('#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5286,c_5286,c_30])).

tff(c_5978,plain,(
    k1_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5968,c_5968,c_5310])).

tff(c_42,plain,(
    ! [A_34] :
      ( v1_funct_2(k1_xboole_0,A_34,k1_xboole_0)
      | k1_xboole_0 = A_34
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(A_34,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_66,plain,(
    ! [A_34] :
      ( v1_funct_2(k1_xboole_0,A_34,k1_xboole_0)
      | k1_xboole_0 = A_34
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_42])).

tff(c_1545,plain,(
    ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitLeft,[status(thm)],[c_66])).

tff(c_1548,plain,(
    ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_18,c_1545])).

tff(c_1552,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_1548])).

tff(c_1554,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_5301,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5286,c_5286,c_1554])).

tff(c_5974,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5968,c_5968,c_5301])).

tff(c_5983,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5968,c_5286])).

tff(c_14,plain,(
    ! [B_4] : k2_zfmisc_1(k1_xboole_0,B_4) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_3948,plain,(
    ! [B_4,C_440] :
      ( k1_relset_1(k1_xboole_0,B_4,C_440) = k1_relat_1(C_440)
      | ~ m1_subset_1(C_440,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_3941])).

tff(c_6288,plain,(
    ! [B_656,C_657] :
      ( k1_relset_1('#skF_3',B_656,C_657) = k1_relat_1(C_657)
      | ~ m1_subset_1(C_657,k1_zfmisc_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5983,c_5983,c_3948])).

tff(c_6290,plain,(
    ! [B_656] : k1_relset_1('#skF_3',B_656,'#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_5974,c_6288])).

tff(c_6295,plain,(
    ! [B_656] : k1_relset_1('#skF_3',B_656,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5978,c_6290])).

tff(c_46,plain,(
    ! [C_36,B_35] :
      ( v1_funct_2(C_36,k1_xboole_0,B_35)
      | k1_relset_1(k1_xboole_0,B_35,C_36) != k1_xboole_0
      | ~ m1_subset_1(C_36,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_35))) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_64,plain,(
    ! [C_36,B_35] :
      ( v1_funct_2(C_36,k1_xboole_0,B_35)
      | k1_relset_1(k1_xboole_0,B_35,C_36) != k1_xboole_0
      | ~ m1_subset_1(C_36,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_46])).

tff(c_5368,plain,(
    ! [C_36,B_35] :
      ( v1_funct_2(C_36,'#skF_2',B_35)
      | k1_relset_1('#skF_2',B_35,C_36) != '#skF_2'
      | ~ m1_subset_1(C_36,k1_zfmisc_1('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5286,c_5286,c_5286,c_5286,c_64])).

tff(c_5382,plain,(
    ! [B_35] :
      ( v1_funct_2('#skF_2','#skF_2',B_35)
      | k1_relset_1('#skF_2',B_35,'#skF_2') != '#skF_2' ) ),
    inference(resolution,[status(thm)],[c_5301,c_5368])).

tff(c_6281,plain,(
    ! [B_655] :
      ( v1_funct_2('#skF_3','#skF_3',B_655)
      | k1_relset_1('#skF_3',B_655,'#skF_3') != '#skF_3' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5968,c_5968,c_5968,c_5968,c_5968,c_5382])).

tff(c_5985,plain,(
    ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5968,c_99])).

tff(c_6020,plain,(
    ~ v1_funct_2('#skF_3','#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5978,c_5985])).

tff(c_6285,plain,(
    k1_relset_1('#skF_3','#skF_3','#skF_3') != '#skF_3' ),
    inference(resolution,[status(thm)],[c_6281,c_6020])).

tff(c_6301,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6295,c_6285])).

tff(c_6302,plain,(
    ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_6612,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_3'),'#skF_2')
    | ~ r1_tarski(k1_relat_1('#skF_3'),k1_relat_1('#skF_3'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_6601,c_6302])).

tff(c_6625,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_8,c_56,c_6612])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:23:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.38/2.24  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.38/2.26  
% 6.38/2.26  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.38/2.26  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k3_mcart_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3
% 6.38/2.26  
% 6.38/2.26  %Foreground sorts:
% 6.38/2.26  
% 6.38/2.26  
% 6.38/2.26  %Background operators:
% 6.38/2.26  
% 6.38/2.26  
% 6.38/2.26  %Foreground operators:
% 6.38/2.26  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 6.38/2.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.38/2.26  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.38/2.26  tff('#skF_1', type, '#skF_1': $i > $i).
% 6.38/2.26  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.38/2.26  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 6.38/2.26  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.38/2.26  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 6.38/2.26  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 6.38/2.26  tff('#skF_2', type, '#skF_2': $i).
% 6.38/2.26  tff('#skF_3', type, '#skF_3': $i).
% 6.38/2.26  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 6.38/2.26  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.38/2.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.38/2.26  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.38/2.26  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.38/2.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.38/2.26  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 6.38/2.26  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 6.38/2.26  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.38/2.26  
% 6.66/2.30  tff(f_126, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(k2_relat_1(B), A) => ((v1_funct_1(B) & v1_funct_2(B, k1_relat_1(B), A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B), A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_funct_2)).
% 6.66/2.30  tff(f_32, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 6.66/2.30  tff(f_79, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_relset_1)).
% 6.66/2.30  tff(f_95, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D, E]: ~((r2_hidden(C, A) | r2_hidden(D, A)) & (B = k3_mcart_1(C, D, E)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_mcart_1)).
% 6.66/2.30  tff(f_42, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 6.66/2.30  tff(f_49, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 6.66/2.30  tff(f_64, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => (r1_tarski(k1_relat_1(A), k1_relat_1(B)) & r1_tarski(k2_relat_1(A), k2_relat_1(B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_relat_1)).
% 6.66/2.30  tff(f_113, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 6.66/2.30  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 6.66/2.30  tff(f_71, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 6.66/2.30  tff(f_38, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 6.66/2.30  tff(f_53, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relat_1)).
% 6.66/2.30  tff(f_67, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 6.66/2.30  tff(c_60, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_126])).
% 6.66/2.30  tff(c_8, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.66/2.30  tff(c_56, plain, (r1_tarski(k2_relat_1('#skF_3'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_126])).
% 6.66/2.30  tff(c_6601, plain, (![C_716, A_717, B_718]: (m1_subset_1(C_716, k1_zfmisc_1(k2_zfmisc_1(A_717, B_718))) | ~r1_tarski(k2_relat_1(C_716), B_718) | ~r1_tarski(k1_relat_1(C_716), A_717) | ~v1_relat_1(C_716))), inference(cnfTransformation, [status(thm)], [f_79])).
% 6.66/2.30  tff(c_58, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_126])).
% 6.66/2.30  tff(c_54, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2'))) | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), '#skF_2') | ~v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_126])).
% 6.66/2.30  tff(c_62, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2'))) | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_54])).
% 6.66/2.30  tff(c_99, plain, (~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), '#skF_2')), inference(splitLeft, [status(thm)], [c_62])).
% 6.66/2.30  tff(c_36, plain, (![A_20]: (r2_hidden('#skF_1'(A_20), A_20) | k1_xboole_0=A_20)), inference(cnfTransformation, [status(thm)], [f_95])).
% 6.66/2.30  tff(c_18, plain, (![A_5, B_6]: (m1_subset_1(A_5, k1_zfmisc_1(B_6)) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_42])).
% 6.66/2.30  tff(c_134, plain, (![C_50, B_51, A_52]: (~v1_xboole_0(C_50) | ~m1_subset_1(B_51, k1_zfmisc_1(C_50)) | ~r2_hidden(A_52, B_51))), inference(cnfTransformation, [status(thm)], [f_49])).
% 6.66/2.30  tff(c_138, plain, (![B_53, A_54, A_55]: (~v1_xboole_0(B_53) | ~r2_hidden(A_54, A_55) | ~r1_tarski(A_55, B_53))), inference(resolution, [status(thm)], [c_18, c_134])).
% 6.66/2.30  tff(c_142, plain, (![B_56, A_57]: (~v1_xboole_0(B_56) | ~r1_tarski(A_57, B_56) | k1_xboole_0=A_57)), inference(resolution, [status(thm)], [c_36, c_138])).
% 6.66/2.30  tff(c_149, plain, (~v1_xboole_0('#skF_2') | k2_relat_1('#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_56, c_142])).
% 6.66/2.30  tff(c_157, plain, (~v1_xboole_0('#skF_2')), inference(splitLeft, [status(thm)], [c_149])).
% 6.66/2.30  tff(c_26, plain, (![A_11, B_13]: (r1_tarski(k1_relat_1(A_11), k1_relat_1(B_13)) | ~r1_tarski(A_11, B_13) | ~v1_relat_1(B_13) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_64])).
% 6.66/2.30  tff(c_468, plain, (![C_111, A_112, B_113]: (m1_subset_1(C_111, k1_zfmisc_1(k2_zfmisc_1(A_112, B_113))) | ~r1_tarski(k2_relat_1(C_111), B_113) | ~r1_tarski(k1_relat_1(C_111), A_112) | ~v1_relat_1(C_111))), inference(cnfTransformation, [status(thm)], [f_79])).
% 6.66/2.30  tff(c_16, plain, (![A_5, B_6]: (r1_tarski(A_5, B_6) | ~m1_subset_1(A_5, k1_zfmisc_1(B_6)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 6.66/2.30  tff(c_705, plain, (![C_144, A_145, B_146]: (r1_tarski(C_144, k2_zfmisc_1(A_145, B_146)) | ~r1_tarski(k2_relat_1(C_144), B_146) | ~r1_tarski(k1_relat_1(C_144), A_145) | ~v1_relat_1(C_144))), inference(resolution, [status(thm)], [c_468, c_16])).
% 6.66/2.30  tff(c_711, plain, (![A_145]: (r1_tarski('#skF_3', k2_zfmisc_1(A_145, '#skF_2')) | ~r1_tarski(k1_relat_1('#skF_3'), A_145) | ~v1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_56, c_705])).
% 6.66/2.30  tff(c_726, plain, (![A_147]: (r1_tarski('#skF_3', k2_zfmisc_1(A_147, '#skF_2')) | ~r1_tarski(k1_relat_1('#skF_3'), A_147))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_711])).
% 6.66/2.30  tff(c_734, plain, (![B_13]: (r1_tarski('#skF_3', k2_zfmisc_1(k1_relat_1(B_13), '#skF_2')) | ~r1_tarski('#skF_3', B_13) | ~v1_relat_1(B_13) | ~v1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_26, c_726])).
% 6.66/2.30  tff(c_745, plain, (![B_13]: (r1_tarski('#skF_3', k2_zfmisc_1(k1_relat_1(B_13), '#skF_2')) | ~r1_tarski('#skF_3', B_13) | ~v1_relat_1(B_13))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_734])).
% 6.66/2.30  tff(c_546, plain, (![B_125, A_126, C_127]: (k1_xboole_0=B_125 | k1_relset_1(A_126, B_125, C_127)=A_126 | ~v1_funct_2(C_127, A_126, B_125) | ~m1_subset_1(C_127, k1_zfmisc_1(k2_zfmisc_1(A_126, B_125))))), inference(cnfTransformation, [status(thm)], [f_113])).
% 6.66/2.30  tff(c_1009, plain, (![B_168, A_169, A_170]: (k1_xboole_0=B_168 | k1_relset_1(A_169, B_168, A_170)=A_169 | ~v1_funct_2(A_170, A_169, B_168) | ~r1_tarski(A_170, k2_zfmisc_1(A_169, B_168)))), inference(resolution, [status(thm)], [c_18, c_546])).
% 6.66/2.30  tff(c_1033, plain, (![B_13]: (k1_xboole_0='#skF_2' | k1_relset_1(k1_relat_1(B_13), '#skF_2', '#skF_3')=k1_relat_1(B_13) | ~v1_funct_2('#skF_3', k1_relat_1(B_13), '#skF_2') | ~r1_tarski('#skF_3', B_13) | ~v1_relat_1(B_13))), inference(resolution, [status(thm)], [c_745, c_1009])).
% 6.66/2.30  tff(c_1381, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_1033])).
% 6.66/2.30  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 6.66/2.30  tff(c_1445, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1381, c_2])).
% 6.66/2.30  tff(c_1447, plain, $false, inference(negUnitSimplification, [status(thm)], [c_157, c_1445])).
% 6.66/2.30  tff(c_1449, plain, (k1_xboole_0!='#skF_2'), inference(splitRight, [status(thm)], [c_1033])).
% 6.66/2.30  tff(c_746, plain, (r1_tarski('#skF_3', k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2'))), inference(resolution, [status(thm)], [c_8, c_726])).
% 6.66/2.30  tff(c_243, plain, (![A_79, B_80, C_81]: (k1_relset_1(A_79, B_80, C_81)=k1_relat_1(C_81) | ~m1_subset_1(C_81, k1_zfmisc_1(k2_zfmisc_1(A_79, B_80))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 6.66/2.30  tff(c_254, plain, (![A_79, B_80, A_5]: (k1_relset_1(A_79, B_80, A_5)=k1_relat_1(A_5) | ~r1_tarski(A_5, k2_zfmisc_1(A_79, B_80)))), inference(resolution, [status(thm)], [c_18, c_243])).
% 6.66/2.30  tff(c_755, plain, (k1_relset_1(k1_relat_1('#skF_3'), '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_746, c_254])).
% 6.66/2.30  tff(c_647, plain, (![B_138, C_139, A_140]: (k1_xboole_0=B_138 | v1_funct_2(C_139, A_140, B_138) | k1_relset_1(A_140, B_138, C_139)!=A_140 | ~m1_subset_1(C_139, k1_zfmisc_1(k2_zfmisc_1(A_140, B_138))))), inference(cnfTransformation, [status(thm)], [f_113])).
% 6.66/2.30  tff(c_1450, plain, (![B_193, A_194, A_195]: (k1_xboole_0=B_193 | v1_funct_2(A_194, A_195, B_193) | k1_relset_1(A_195, B_193, A_194)!=A_195 | ~r1_tarski(A_194, k2_zfmisc_1(A_195, B_193)))), inference(resolution, [status(thm)], [c_18, c_647])).
% 6.66/2.30  tff(c_1462, plain, (k1_xboole_0='#skF_2' | v1_funct_2('#skF_3', k1_relat_1('#skF_3'), '#skF_2') | k1_relset_1(k1_relat_1('#skF_3'), '#skF_2', '#skF_3')!=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_746, c_1450])).
% 6.66/2.30  tff(c_1480, plain, (k1_xboole_0='#skF_2' | v1_funct_2('#skF_3', k1_relat_1('#skF_3'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_755, c_1462])).
% 6.66/2.30  tff(c_1482, plain, $false, inference(negUnitSimplification, [status(thm)], [c_99, c_1449, c_1480])).
% 6.66/2.30  tff(c_1484, plain, (v1_xboole_0('#skF_2')), inference(splitRight, [status(thm)], [c_149])).
% 6.66/2.30  tff(c_150, plain, (![B_2]: (~v1_xboole_0(B_2) | k1_xboole_0=B_2)), inference(resolution, [status(thm)], [c_8, c_142])).
% 6.66/2.30  tff(c_1491, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_1484, c_150])).
% 6.66/2.30  tff(c_1483, plain, (k2_relat_1('#skF_3')=k1_xboole_0), inference(splitRight, [status(thm)], [c_149])).
% 6.66/2.30  tff(c_1511, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_1491, c_1483])).
% 6.66/2.30  tff(c_123, plain, (![B_48, A_49]: (B_48=A_49 | ~r1_tarski(B_48, A_49) | ~r1_tarski(A_49, B_48))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.66/2.30  tff(c_128, plain, (k2_relat_1('#skF_3')='#skF_2' | ~r1_tarski('#skF_2', k2_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_56, c_123])).
% 6.66/2.30  tff(c_133, plain, (~r1_tarski('#skF_2', k2_relat_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_128])).
% 6.66/2.30  tff(c_1512, plain, (~r1_tarski('#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1511, c_133])).
% 6.66/2.30  tff(c_1516, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8, c_1512])).
% 6.66/2.30  tff(c_1517, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(splitRight, [status(thm)], [c_128])).
% 6.66/2.30  tff(c_4222, plain, (![C_470, A_471, B_472]: (m1_subset_1(C_470, k1_zfmisc_1(k2_zfmisc_1(A_471, B_472))) | ~r1_tarski(k2_relat_1(C_470), B_472) | ~r1_tarski(k1_relat_1(C_470), A_471) | ~v1_relat_1(C_470))), inference(cnfTransformation, [status(thm)], [f_79])).
% 6.66/2.30  tff(c_4516, plain, (![C_504, A_505, B_506]: (r1_tarski(C_504, k2_zfmisc_1(A_505, B_506)) | ~r1_tarski(k2_relat_1(C_504), B_506) | ~r1_tarski(k1_relat_1(C_504), A_505) | ~v1_relat_1(C_504))), inference(resolution, [status(thm)], [c_4222, c_16])).
% 6.66/2.30  tff(c_4982, plain, (![C_536, A_537]: (r1_tarski(C_536, k2_zfmisc_1(A_537, k2_relat_1(C_536))) | ~r1_tarski(k1_relat_1(C_536), A_537) | ~v1_relat_1(C_536))), inference(resolution, [status(thm)], [c_8, c_4516])).
% 6.66/2.30  tff(c_5020, plain, (![A_537]: (r1_tarski('#skF_3', k2_zfmisc_1(A_537, '#skF_2')) | ~r1_tarski(k1_relat_1('#skF_3'), A_537) | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1517, c_4982])).
% 6.66/2.30  tff(c_5059, plain, (![A_539]: (r1_tarski('#skF_3', k2_zfmisc_1(A_539, '#skF_2')) | ~r1_tarski(k1_relat_1('#skF_3'), A_539))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_5020])).
% 6.66/2.30  tff(c_5089, plain, (r1_tarski('#skF_3', k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2'))), inference(resolution, [status(thm)], [c_8, c_5059])).
% 6.66/2.30  tff(c_3941, plain, (![A_438, B_439, C_440]: (k1_relset_1(A_438, B_439, C_440)=k1_relat_1(C_440) | ~m1_subset_1(C_440, k1_zfmisc_1(k2_zfmisc_1(A_438, B_439))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 6.66/2.30  tff(c_3952, plain, (![A_438, B_439, A_5]: (k1_relset_1(A_438, B_439, A_5)=k1_relat_1(A_5) | ~r1_tarski(A_5, k2_zfmisc_1(A_438, B_439)))), inference(resolution, [status(thm)], [c_18, c_3941])).
% 6.66/2.30  tff(c_5118, plain, (k1_relset_1(k1_relat_1('#skF_3'), '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_5089, c_3952])).
% 6.66/2.30  tff(c_4320, plain, (![B_480, C_481, A_482]: (k1_xboole_0=B_480 | v1_funct_2(C_481, A_482, B_480) | k1_relset_1(A_482, B_480, C_481)!=A_482 | ~m1_subset_1(C_481, k1_zfmisc_1(k2_zfmisc_1(A_482, B_480))))), inference(cnfTransformation, [status(thm)], [f_113])).
% 6.66/2.30  tff(c_5169, plain, (![B_543, A_544, A_545]: (k1_xboole_0=B_543 | v1_funct_2(A_544, A_545, B_543) | k1_relset_1(A_545, B_543, A_544)!=A_545 | ~r1_tarski(A_544, k2_zfmisc_1(A_545, B_543)))), inference(resolution, [status(thm)], [c_18, c_4320])).
% 6.66/2.30  tff(c_5172, plain, (k1_xboole_0='#skF_2' | v1_funct_2('#skF_3', k1_relat_1('#skF_3'), '#skF_2') | k1_relset_1(k1_relat_1('#skF_3'), '#skF_2', '#skF_3')!=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_5089, c_5169])).
% 6.66/2.30  tff(c_5200, plain, (k1_xboole_0='#skF_2' | v1_funct_2('#skF_3', k1_relat_1('#skF_3'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_5118, c_5172])).
% 6.66/2.30  tff(c_5201, plain, (k1_xboole_0='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_99, c_5200])).
% 6.66/2.30  tff(c_1649, plain, (![A_228, B_229]: (r1_tarski(k2_relat_1(A_228), k2_relat_1(B_229)) | ~r1_tarski(A_228, B_229) | ~v1_relat_1(B_229) | ~v1_relat_1(A_228))), inference(cnfTransformation, [status(thm)], [f_64])).
% 6.66/2.30  tff(c_1660, plain, (![A_228]: (r1_tarski(k2_relat_1(A_228), '#skF_2') | ~r1_tarski(A_228, '#skF_3') | ~v1_relat_1('#skF_3') | ~v1_relat_1(A_228))), inference(superposition, [status(thm), theory('equality')], [c_1517, c_1649])).
% 6.66/2.30  tff(c_1750, plain, (![A_236]: (r1_tarski(k2_relat_1(A_236), '#skF_2') | ~r1_tarski(A_236, '#skF_3') | ~v1_relat_1(A_236))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_1660])).
% 6.66/2.30  tff(c_1526, plain, (![C_196, B_197, A_198]: (~v1_xboole_0(C_196) | ~m1_subset_1(B_197, k1_zfmisc_1(C_196)) | ~r2_hidden(A_198, B_197))), inference(cnfTransformation, [status(thm)], [f_49])).
% 6.66/2.30  tff(c_1530, plain, (![B_199, A_200, A_201]: (~v1_xboole_0(B_199) | ~r2_hidden(A_200, A_201) | ~r1_tarski(A_201, B_199))), inference(resolution, [status(thm)], [c_18, c_1526])).
% 6.66/2.30  tff(c_1533, plain, (![B_199, A_20]: (~v1_xboole_0(B_199) | ~r1_tarski(A_20, B_199) | k1_xboole_0=A_20)), inference(resolution, [status(thm)], [c_36, c_1530])).
% 6.66/2.30  tff(c_1762, plain, (![A_236]: (~v1_xboole_0('#skF_2') | k2_relat_1(A_236)=k1_xboole_0 | ~r1_tarski(A_236, '#skF_3') | ~v1_relat_1(A_236))), inference(resolution, [status(thm)], [c_1750, c_1533])).
% 6.66/2.30  tff(c_1868, plain, (~v1_xboole_0('#skF_2')), inference(splitLeft, [status(thm)], [c_1762])).
% 6.66/2.30  tff(c_2011, plain, (![C_268, A_269, B_270]: (m1_subset_1(C_268, k1_zfmisc_1(k2_zfmisc_1(A_269, B_270))) | ~r1_tarski(k2_relat_1(C_268), B_270) | ~r1_tarski(k1_relat_1(C_268), A_269) | ~v1_relat_1(C_268))), inference(cnfTransformation, [status(thm)], [f_79])).
% 6.66/2.30  tff(c_2237, plain, (![C_296, A_297, B_298]: (r1_tarski(C_296, k2_zfmisc_1(A_297, B_298)) | ~r1_tarski(k2_relat_1(C_296), B_298) | ~r1_tarski(k1_relat_1(C_296), A_297) | ~v1_relat_1(C_296))), inference(resolution, [status(thm)], [c_2011, c_16])).
% 6.66/2.30  tff(c_2332, plain, (![C_305, A_306]: (r1_tarski(C_305, k2_zfmisc_1(A_306, k2_relat_1(C_305))) | ~r1_tarski(k1_relat_1(C_305), A_306) | ~v1_relat_1(C_305))), inference(resolution, [status(thm)], [c_8, c_2237])).
% 6.66/2.30  tff(c_2349, plain, (![A_306]: (r1_tarski('#skF_3', k2_zfmisc_1(A_306, '#skF_2')) | ~r1_tarski(k1_relat_1('#skF_3'), A_306) | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1517, c_2332])).
% 6.66/2.30  tff(c_2368, plain, (![A_307]: (r1_tarski('#skF_3', k2_zfmisc_1(A_307, '#skF_2')) | ~r1_tarski(k1_relat_1('#skF_3'), A_307))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_2349])).
% 6.66/2.30  tff(c_2393, plain, (r1_tarski('#skF_3', k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2'))), inference(resolution, [status(thm)], [c_8, c_2368])).
% 6.66/2.30  tff(c_1722, plain, (![A_232, B_233, C_234]: (k1_relset_1(A_232, B_233, C_234)=k1_relat_1(C_234) | ~m1_subset_1(C_234, k1_zfmisc_1(k2_zfmisc_1(A_232, B_233))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 6.66/2.30  tff(c_1733, plain, (![A_232, B_233, A_5]: (k1_relset_1(A_232, B_233, A_5)=k1_relat_1(A_5) | ~r1_tarski(A_5, k2_zfmisc_1(A_232, B_233)))), inference(resolution, [status(thm)], [c_18, c_1722])).
% 6.66/2.30  tff(c_2402, plain, (k1_relset_1(k1_relat_1('#skF_3'), '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_2393, c_1733])).
% 6.66/2.30  tff(c_2051, plain, (![B_275, C_276, A_277]: (k1_xboole_0=B_275 | v1_funct_2(C_276, A_277, B_275) | k1_relset_1(A_277, B_275, C_276)!=A_277 | ~m1_subset_1(C_276, k1_zfmisc_1(k2_zfmisc_1(A_277, B_275))))), inference(cnfTransformation, [status(thm)], [f_113])).
% 6.66/2.30  tff(c_2420, plain, (![B_309, A_310, A_311]: (k1_xboole_0=B_309 | v1_funct_2(A_310, A_311, B_309) | k1_relset_1(A_311, B_309, A_310)!=A_311 | ~r1_tarski(A_310, k2_zfmisc_1(A_311, B_309)))), inference(resolution, [status(thm)], [c_18, c_2051])).
% 6.66/2.30  tff(c_2423, plain, (k1_xboole_0='#skF_2' | v1_funct_2('#skF_3', k1_relat_1('#skF_3'), '#skF_2') | k1_relset_1(k1_relat_1('#skF_3'), '#skF_2', '#skF_3')!=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_2393, c_2420])).
% 6.66/2.30  tff(c_2442, plain, (k1_xboole_0='#skF_2' | v1_funct_2('#skF_3', k1_relat_1('#skF_3'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2402, c_2423])).
% 6.66/2.30  tff(c_2443, plain, (k1_xboole_0='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_99, c_2442])).
% 6.66/2.30  tff(c_12, plain, (![A_3]: (k2_zfmisc_1(A_3, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_38])).
% 6.66/2.30  tff(c_2224, plain, (![C_294, A_295]: (m1_subset_1(C_294, k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski(k2_relat_1(C_294), k1_xboole_0) | ~r1_tarski(k1_relat_1(C_294), A_295) | ~v1_relat_1(C_294))), inference(superposition, [status(thm), theory('equality')], [c_12, c_2011])).
% 6.66/2.30  tff(c_2228, plain, (![A_295]: (m1_subset_1('#skF_3', k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski('#skF_2', k1_xboole_0) | ~r1_tarski(k1_relat_1('#skF_3'), A_295) | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1517, c_2224])).
% 6.66/2.30  tff(c_2233, plain, (![A_295]: (m1_subset_1('#skF_3', k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski('#skF_2', k1_xboole_0) | ~r1_tarski(k1_relat_1('#skF_3'), A_295))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_2228])).
% 6.66/2.30  tff(c_2236, plain, (~r1_tarski('#skF_2', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_2233])).
% 6.66/2.30  tff(c_2453, plain, (~r1_tarski('#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2443, c_2236])).
% 6.66/2.30  tff(c_2509, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8, c_2453])).
% 6.66/2.30  tff(c_2511, plain, (r1_tarski('#skF_2', k1_xboole_0)), inference(splitRight, [status(thm)], [c_2233])).
% 6.66/2.30  tff(c_2524, plain, (~v1_xboole_0(k1_xboole_0) | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_2511, c_1533])).
% 6.66/2.30  tff(c_2533, plain, (k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_2, c_2524])).
% 6.66/2.30  tff(c_2588, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2533, c_2])).
% 6.66/2.30  tff(c_2591, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1868, c_2588])).
% 6.66/2.30  tff(c_2593, plain, (v1_xboole_0('#skF_2')), inference(splitRight, [status(thm)], [c_1762])).
% 6.66/2.30  tff(c_1657, plain, (![B_229]: (r1_tarski('#skF_2', k2_relat_1(B_229)) | ~r1_tarski('#skF_3', B_229) | ~v1_relat_1(B_229) | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1517, c_1649])).
% 6.66/2.30  tff(c_1768, plain, (![B_237]: (r1_tarski('#skF_2', k2_relat_1(B_237)) | ~r1_tarski('#skF_3', B_237) | ~v1_relat_1(B_237))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_1657])).
% 6.66/2.30  tff(c_1780, plain, (![B_237]: (~v1_xboole_0(k2_relat_1(B_237)) | k1_xboole_0='#skF_2' | ~r1_tarski('#skF_3', B_237) | ~v1_relat_1(B_237))), inference(resolution, [status(thm)], [c_1768, c_1533])).
% 6.66/2.30  tff(c_2866, plain, (![B_334]: (~v1_xboole_0(k2_relat_1(B_334)) | ~r1_tarski('#skF_3', B_334) | ~v1_relat_1(B_334))), inference(splitLeft, [status(thm)], [c_1780])).
% 6.66/2.30  tff(c_2872, plain, (~v1_xboole_0('#skF_2') | ~r1_tarski('#skF_3', '#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1517, c_2866])).
% 6.66/2.30  tff(c_2877, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_60, c_8, c_2593, c_2872])).
% 6.66/2.30  tff(c_2878, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_1780])).
% 6.66/2.30  tff(c_100, plain, (![A_40]: (v1_relat_1(A_40) | ~v1_xboole_0(A_40))), inference(cnfTransformation, [status(thm)], [f_53])).
% 6.66/2.30  tff(c_104, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_100])).
% 6.66/2.30  tff(c_28, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_67])).
% 6.66/2.30  tff(c_1666, plain, (![A_228]: (r1_tarski(k2_relat_1(A_228), k1_xboole_0) | ~r1_tarski(A_228, k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_228))), inference(superposition, [status(thm), theory('equality')], [c_28, c_1649])).
% 6.66/2.30  tff(c_1697, plain, (![A_231]: (r1_tarski(k2_relat_1(A_231), k1_xboole_0) | ~r1_tarski(A_231, k1_xboole_0) | ~v1_relat_1(A_231))), inference(demodulation, [status(thm), theory('equality')], [c_104, c_1666])).
% 6.66/2.30  tff(c_1708, plain, (r1_tarski('#skF_2', k1_xboole_0) | ~r1_tarski('#skF_3', k1_xboole_0) | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1517, c_1697])).
% 6.66/2.30  tff(c_1718, plain, (r1_tarski('#skF_2', k1_xboole_0) | ~r1_tarski('#skF_3', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_60, c_1708])).
% 6.66/2.30  tff(c_1721, plain, (~r1_tarski('#skF_3', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_1718])).
% 6.66/2.30  tff(c_2911, plain, (~r1_tarski('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2878, c_1721])).
% 6.66/2.30  tff(c_2932, plain, (![A_3]: (k2_zfmisc_1(A_3, '#skF_2')='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2878, c_2878, c_12])).
% 6.66/2.30  tff(c_3034, plain, (![C_344, A_345, B_346]: (m1_subset_1(C_344, k1_zfmisc_1(k2_zfmisc_1(A_345, B_346))) | ~r1_tarski(k2_relat_1(C_344), B_346) | ~r1_tarski(k1_relat_1(C_344), A_345) | ~v1_relat_1(C_344))), inference(cnfTransformation, [status(thm)], [f_79])).
% 6.66/2.30  tff(c_3551, plain, (![C_411, A_412, B_413]: (r1_tarski(C_411, k2_zfmisc_1(A_412, B_413)) | ~r1_tarski(k2_relat_1(C_411), B_413) | ~r1_tarski(k1_relat_1(C_411), A_412) | ~v1_relat_1(C_411))), inference(resolution, [status(thm)], [c_3034, c_16])).
% 6.66/2.30  tff(c_3617, plain, (![C_418, A_419]: (r1_tarski(C_418, k2_zfmisc_1(A_419, k2_relat_1(C_418))) | ~r1_tarski(k1_relat_1(C_418), A_419) | ~v1_relat_1(C_418))), inference(resolution, [status(thm)], [c_8, c_3551])).
% 6.66/2.30  tff(c_3641, plain, (![A_419]: (r1_tarski('#skF_3', k2_zfmisc_1(A_419, '#skF_2')) | ~r1_tarski(k1_relat_1('#skF_3'), A_419) | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1517, c_3617])).
% 6.66/2.30  tff(c_3652, plain, (![A_419]: (r1_tarski('#skF_3', '#skF_2') | ~r1_tarski(k1_relat_1('#skF_3'), A_419))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_2932, c_3641])).
% 6.66/2.30  tff(c_3676, plain, (![A_422]: (~r1_tarski(k1_relat_1('#skF_3'), A_422))), inference(negUnitSimplification, [status(thm)], [c_2911, c_3652])).
% 6.66/2.30  tff(c_3700, plain, $false, inference(resolution, [status(thm)], [c_8, c_3676])).
% 6.66/2.30  tff(c_3701, plain, (r1_tarski('#skF_2', k1_xboole_0)), inference(splitRight, [status(thm)], [c_1718])).
% 6.66/2.30  tff(c_3708, plain, (~v1_xboole_0(k1_xboole_0) | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_3701, c_1533])).
% 6.66/2.30  tff(c_3714, plain, (k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_2, c_3708])).
% 6.66/2.30  tff(c_3740, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_3714, c_2])).
% 6.66/2.30  tff(c_3702, plain, (r1_tarski('#skF_3', k1_xboole_0)), inference(splitRight, [status(thm)], [c_1718])).
% 6.66/2.30  tff(c_3757, plain, (r1_tarski('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_3714, c_3702])).
% 6.66/2.30  tff(c_3886, plain, (![B_436, A_437]: (~v1_xboole_0(B_436) | ~r1_tarski(A_437, B_436) | A_437='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_3714, c_1533])).
% 6.66/2.30  tff(c_3895, plain, (~v1_xboole_0('#skF_2') | '#skF_2'='#skF_3'), inference(resolution, [status(thm)], [c_3757, c_3886])).
% 6.66/2.30  tff(c_3912, plain, ('#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_3740, c_3895])).
% 6.66/2.30  tff(c_1663, plain, (![B_229]: (r1_tarski(k1_xboole_0, k2_relat_1(B_229)) | ~r1_tarski(k1_xboole_0, B_229) | ~v1_relat_1(B_229) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_28, c_1649])).
% 6.66/2.30  tff(c_1677, plain, (![B_230]: (r1_tarski(k1_xboole_0, k2_relat_1(B_230)) | ~r1_tarski(k1_xboole_0, B_230) | ~v1_relat_1(B_230))), inference(demodulation, [status(thm), theory('equality')], [c_104, c_1663])).
% 6.66/2.30  tff(c_1685, plain, (r1_tarski(k1_xboole_0, '#skF_2') | ~r1_tarski(k1_xboole_0, '#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1517, c_1677])).
% 6.66/2.30  tff(c_1693, plain, (r1_tarski(k1_xboole_0, '#skF_2') | ~r1_tarski(k1_xboole_0, '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_1685])).
% 6.66/2.30  tff(c_1696, plain, (~r1_tarski(k1_xboole_0, '#skF_3')), inference(splitLeft, [status(thm)], [c_1693])).
% 6.66/2.30  tff(c_3718, plain, (~r1_tarski('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_3714, c_1696])).
% 6.66/2.30  tff(c_3925, plain, (~r1_tarski('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_3912, c_3718])).
% 6.66/2.30  tff(c_3938, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8, c_3925])).
% 6.66/2.30  tff(c_3939, plain, (r1_tarski(k1_xboole_0, '#skF_2')), inference(splitRight, [status(thm)], [c_1693])).
% 6.66/2.30  tff(c_4, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.66/2.30  tff(c_3960, plain, (k1_xboole_0='#skF_2' | ~r1_tarski('#skF_2', k1_xboole_0)), inference(resolution, [status(thm)], [c_3939, c_4])).
% 6.66/2.30  tff(c_3969, plain, (~r1_tarski('#skF_2', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_3960])).
% 6.66/2.30  tff(c_5258, plain, (~r1_tarski('#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_5201, c_3969])).
% 6.66/2.30  tff(c_5285, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8, c_5258])).
% 6.66/2.30  tff(c_5286, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_3960])).
% 6.66/2.30  tff(c_3940, plain, (r1_tarski(k1_xboole_0, '#skF_3')), inference(splitRight, [status(thm)], [c_1693])).
% 6.66/2.30  tff(c_3968, plain, (k1_xboole_0='#skF_3' | ~r1_tarski('#skF_3', k1_xboole_0)), inference(resolution, [status(thm)], [c_3940, c_4])).
% 6.66/2.30  tff(c_5436, plain, ('#skF_2'='#skF_3' | ~r1_tarski('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_5286, c_5286, c_3968])).
% 6.66/2.30  tff(c_5437, plain, (~r1_tarski('#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_5436])).
% 6.66/2.30  tff(c_5308, plain, (![A_3]: (k2_zfmisc_1(A_3, '#skF_2')='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_5286, c_5286, c_12])).
% 6.66/2.30  tff(c_5568, plain, (![C_566, A_567, B_568]: (m1_subset_1(C_566, k1_zfmisc_1(k2_zfmisc_1(A_567, B_568))) | ~r1_tarski(k2_relat_1(C_566), B_568) | ~r1_tarski(k1_relat_1(C_566), A_567) | ~v1_relat_1(C_566))), inference(cnfTransformation, [status(thm)], [f_79])).
% 6.66/2.30  tff(c_5830, plain, (![C_611, A_612, B_613]: (r1_tarski(C_611, k2_zfmisc_1(A_612, B_613)) | ~r1_tarski(k2_relat_1(C_611), B_613) | ~r1_tarski(k1_relat_1(C_611), A_612) | ~v1_relat_1(C_611))), inference(resolution, [status(thm)], [c_5568, c_16])).
% 6.66/2.30  tff(c_5840, plain, (![A_612, B_613]: (r1_tarski('#skF_3', k2_zfmisc_1(A_612, B_613)) | ~r1_tarski('#skF_2', B_613) | ~r1_tarski(k1_relat_1('#skF_3'), A_612) | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1517, c_5830])).
% 6.66/2.30  tff(c_5899, plain, (![A_618, B_619]: (r1_tarski('#skF_3', k2_zfmisc_1(A_618, B_619)) | ~r1_tarski('#skF_2', B_619) | ~r1_tarski(k1_relat_1('#skF_3'), A_618))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_5840])).
% 6.66/2.30  tff(c_5948, plain, (![B_621]: (r1_tarski('#skF_3', k2_zfmisc_1(k1_relat_1('#skF_3'), B_621)) | ~r1_tarski('#skF_2', B_621))), inference(resolution, [status(thm)], [c_8, c_5899])).
% 6.66/2.30  tff(c_5960, plain, (r1_tarski('#skF_3', '#skF_2') | ~r1_tarski('#skF_2', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_5308, c_5948])).
% 6.66/2.30  tff(c_5965, plain, (r1_tarski('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_8, c_5960])).
% 6.66/2.30  tff(c_5967, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5437, c_5965])).
% 6.66/2.30  tff(c_5968, plain, ('#skF_2'='#skF_3'), inference(splitRight, [status(thm)], [c_5436])).
% 6.66/2.30  tff(c_30, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_67])).
% 6.66/2.30  tff(c_5310, plain, (k1_relat_1('#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_5286, c_5286, c_30])).
% 6.66/2.30  tff(c_5978, plain, (k1_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_5968, c_5968, c_5310])).
% 6.66/2.30  tff(c_42, plain, (![A_34]: (v1_funct_2(k1_xboole_0, A_34, k1_xboole_0) | k1_xboole_0=A_34 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(A_34, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_113])).
% 6.66/2.30  tff(c_66, plain, (![A_34]: (v1_funct_2(k1_xboole_0, A_34, k1_xboole_0) | k1_xboole_0=A_34 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_42])).
% 6.66/2.30  tff(c_1545, plain, (~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0))), inference(splitLeft, [status(thm)], [c_66])).
% 6.66/2.30  tff(c_1548, plain, (~r1_tarski(k1_xboole_0, k1_xboole_0)), inference(resolution, [status(thm)], [c_18, c_1545])).
% 6.66/2.30  tff(c_1552, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8, c_1548])).
% 6.66/2.30  tff(c_1554, plain, (m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0))), inference(splitRight, [status(thm)], [c_66])).
% 6.66/2.30  tff(c_5301, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_5286, c_5286, c_1554])).
% 6.66/2.30  tff(c_5974, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_5968, c_5968, c_5301])).
% 6.66/2.30  tff(c_5983, plain, (k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_5968, c_5286])).
% 6.66/2.30  tff(c_14, plain, (![B_4]: (k2_zfmisc_1(k1_xboole_0, B_4)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_38])).
% 6.66/2.30  tff(c_3948, plain, (![B_4, C_440]: (k1_relset_1(k1_xboole_0, B_4, C_440)=k1_relat_1(C_440) | ~m1_subset_1(C_440, k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_3941])).
% 6.66/2.30  tff(c_6288, plain, (![B_656, C_657]: (k1_relset_1('#skF_3', B_656, C_657)=k1_relat_1(C_657) | ~m1_subset_1(C_657, k1_zfmisc_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_5983, c_5983, c_3948])).
% 6.66/2.30  tff(c_6290, plain, (![B_656]: (k1_relset_1('#skF_3', B_656, '#skF_3')=k1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_5974, c_6288])).
% 6.66/2.30  tff(c_6295, plain, (![B_656]: (k1_relset_1('#skF_3', B_656, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_5978, c_6290])).
% 6.66/2.30  tff(c_46, plain, (![C_36, B_35]: (v1_funct_2(C_36, k1_xboole_0, B_35) | k1_relset_1(k1_xboole_0, B_35, C_36)!=k1_xboole_0 | ~m1_subset_1(C_36, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_35))))), inference(cnfTransformation, [status(thm)], [f_113])).
% 6.66/2.30  tff(c_64, plain, (![C_36, B_35]: (v1_funct_2(C_36, k1_xboole_0, B_35) | k1_relset_1(k1_xboole_0, B_35, C_36)!=k1_xboole_0 | ~m1_subset_1(C_36, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_46])).
% 6.66/2.30  tff(c_5368, plain, (![C_36, B_35]: (v1_funct_2(C_36, '#skF_2', B_35) | k1_relset_1('#skF_2', B_35, C_36)!='#skF_2' | ~m1_subset_1(C_36, k1_zfmisc_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_5286, c_5286, c_5286, c_5286, c_64])).
% 6.66/2.30  tff(c_5382, plain, (![B_35]: (v1_funct_2('#skF_2', '#skF_2', B_35) | k1_relset_1('#skF_2', B_35, '#skF_2')!='#skF_2')), inference(resolution, [status(thm)], [c_5301, c_5368])).
% 6.66/2.30  tff(c_6281, plain, (![B_655]: (v1_funct_2('#skF_3', '#skF_3', B_655) | k1_relset_1('#skF_3', B_655, '#skF_3')!='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_5968, c_5968, c_5968, c_5968, c_5968, c_5382])).
% 6.66/2.30  tff(c_5985, plain, (~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_5968, c_99])).
% 6.66/2.30  tff(c_6020, plain, (~v1_funct_2('#skF_3', '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_5978, c_5985])).
% 6.66/2.30  tff(c_6285, plain, (k1_relset_1('#skF_3', '#skF_3', '#skF_3')!='#skF_3'), inference(resolution, [status(thm)], [c_6281, c_6020])).
% 6.66/2.30  tff(c_6301, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6295, c_6285])).
% 6.66/2.30  tff(c_6302, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2')))), inference(splitRight, [status(thm)], [c_62])).
% 6.66/2.30  tff(c_6612, plain, (~r1_tarski(k2_relat_1('#skF_3'), '#skF_2') | ~r1_tarski(k1_relat_1('#skF_3'), k1_relat_1('#skF_3')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_6601, c_6302])).
% 6.66/2.30  tff(c_6625, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_60, c_8, c_56, c_6612])).
% 6.66/2.30  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.66/2.30  
% 6.66/2.30  Inference rules
% 6.66/2.30  ----------------------
% 6.66/2.30  #Ref     : 0
% 6.66/2.30  #Sup     : 1306
% 6.66/2.30  #Fact    : 0
% 6.66/2.30  #Define  : 0
% 6.66/2.30  #Split   : 30
% 6.66/2.30  #Chain   : 0
% 6.66/2.30  #Close   : 0
% 6.66/2.30  
% 6.66/2.30  Ordering : KBO
% 6.66/2.30  
% 6.66/2.30  Simplification rules
% 6.66/2.30  ----------------------
% 6.66/2.30  #Subsume      : 218
% 6.66/2.30  #Demod        : 2013
% 6.66/2.30  #Tautology    : 583
% 6.66/2.30  #SimpNegUnit  : 18
% 6.66/2.30  #BackRed      : 421
% 6.66/2.30  
% 6.66/2.30  #Partial instantiations: 0
% 6.66/2.30  #Strategies tried      : 1
% 6.66/2.30  
% 6.66/2.30  Timing (in seconds)
% 6.66/2.30  ----------------------
% 6.66/2.30  Preprocessing        : 0.31
% 6.66/2.30  Parsing              : 0.16
% 6.66/2.30  CNF conversion       : 0.02
% 6.66/2.30  Main loop            : 1.17
% 6.66/2.30  Inferencing          : 0.40
% 6.66/2.30  Reduction            : 0.37
% 6.66/2.30  Demodulation         : 0.26
% 6.66/2.30  BG Simplification    : 0.05
% 6.66/2.30  Subsumption          : 0.25
% 6.66/2.30  Abstraction          : 0.06
% 6.66/2.30  MUC search           : 0.00
% 6.66/2.30  Cooper               : 0.00
% 6.66/2.30  Total                : 1.55
% 6.66/2.30  Index Insertion      : 0.00
% 6.66/2.30  Index Deletion       : 0.00
% 6.66/2.30  Index Matching       : 0.00
% 6.66/2.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
