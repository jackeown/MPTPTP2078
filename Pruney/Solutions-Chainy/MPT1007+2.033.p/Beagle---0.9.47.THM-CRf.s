%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:15 EST 2020

% Result     : Theorem 3.23s
% Output     : CNFRefutation 3.36s
% Verified   : 
% Statistics : Number of formulae       :  116 ( 447 expanded)
%              Number of leaves         :   48 ( 166 expanded)
%              Depth                    :   18
%              Number of atoms          :  198 ( 978 expanded)
%              Number of equality atoms :   66 ( 346 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v5_ordinal1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k4_tarski > k2_zfmisc_1 > k2_tarski > k1_funct_1 > k11_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(v5_ordinal1,type,(
    v5_ordinal1: $i > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k11_relat_1,type,(
    k11_relat_1: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

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

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_154,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,k1_tarski(A),B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => r2_hidden(k1_funct_1(C,A),B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_2)).

tff(f_124,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_78,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_130,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_50,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] : k11_relat_1(A,B) = k9_relat_1(A,k1_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_relat_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r2_hidden(A,k1_relat_1(B))
      <=> k11_relat_1(B,A) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t205_relat_1)).

tff(f_107,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A)
        & v1_funct_1(B) )
     => ! [C] :
          ( r2_hidden(C,k1_relat_1(B))
         => r2_hidden(k1_funct_1(B,C),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t172_funct_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_36,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_70,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_120,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_96,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B,C] :
          ( ( r2_hidden(B,k1_relat_1(A))
           => ( C = k1_funct_1(A,B)
            <=> r2_hidden(k4_tarski(B,C),A) ) )
          & ( ~ r2_hidden(B,k1_relat_1(A))
           => ( C = k1_funct_1(A,B)
            <=> C = k1_xboole_0 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_funct_1)).

tff(f_34,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_142,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_hidden(C,A)
       => ( B = k1_xboole_0
          | r2_hidden(k1_funct_1(D,C),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_funct_2)).

tff(f_45,axiom,(
    ! [A] : ~ v1_xboole_0(k1_tarski(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_xboole_0)).

tff(c_66,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_2'),'#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_129,plain,(
    ! [C_55,A_56,B_57] :
      ( v1_relat_1(C_55)
      | ~ m1_subset_1(C_55,k1_zfmisc_1(k2_zfmisc_1(A_56,B_57))) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_133,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_66,c_129])).

tff(c_30,plain,(
    ! [A_20] :
      ( k2_relat_1(A_20) != k1_xboole_0
      | k1_xboole_0 = A_20
      | ~ v1_relat_1(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_140,plain,
    ( k2_relat_1('#skF_4') != k1_xboole_0
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_133,c_30])).

tff(c_142,plain,(
    k2_relat_1('#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_140])).

tff(c_143,plain,(
    ! [C_58,A_59,B_60] :
      ( v4_relat_1(C_58,A_59)
      | ~ m1_subset_1(C_58,k1_zfmisc_1(k2_zfmisc_1(A_59,B_60))) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_147,plain,(
    v4_relat_1('#skF_4',k1_tarski('#skF_2')) ),
    inference(resolution,[status(thm)],[c_66,c_143])).

tff(c_172,plain,(
    ! [B_68,A_69] :
      ( k7_relat_1(B_68,A_69) = B_68
      | ~ v4_relat_1(B_68,A_69)
      | ~ v1_relat_1(B_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_175,plain,
    ( k7_relat_1('#skF_4',k1_tarski('#skF_2')) = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_147,c_172])).

tff(c_178,plain,(
    k7_relat_1('#skF_4',k1_tarski('#skF_2')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_133,c_175])).

tff(c_18,plain,(
    ! [B_15,A_14] :
      ( k2_relat_1(k7_relat_1(B_15,A_14)) = k9_relat_1(B_15,A_14)
      | ~ v1_relat_1(B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_182,plain,
    ( k9_relat_1('#skF_4',k1_tarski('#skF_2')) = k2_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_178,c_18])).

tff(c_186,plain,(
    k9_relat_1('#skF_4',k1_tarski('#skF_2')) = k2_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_133,c_182])).

tff(c_16,plain,(
    ! [A_11,B_13] :
      ( k9_relat_1(A_11,k1_tarski(B_13)) = k11_relat_1(A_11,B_13)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_200,plain,
    ( k11_relat_1('#skF_4','#skF_2') = k2_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_186,c_16])).

tff(c_207,plain,(
    k11_relat_1('#skF_4','#skF_2') = k2_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_133,c_200])).

tff(c_20,plain,(
    ! [A_16,B_17] :
      ( r2_hidden(A_16,k1_relat_1(B_17))
      | k11_relat_1(B_17,A_16) = k1_xboole_0
      | ~ v1_relat_1(B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_167,plain,(
    ! [C_65,B_66,A_67] :
      ( v5_relat_1(C_65,B_66)
      | ~ m1_subset_1(C_65,k1_zfmisc_1(k2_zfmisc_1(A_67,B_66))) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_171,plain,(
    v5_relat_1('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_167])).

tff(c_70,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_395,plain,(
    ! [B_95,C_96,A_97] :
      ( r2_hidden(k1_funct_1(B_95,C_96),A_97)
      | ~ r2_hidden(C_96,k1_relat_1(B_95))
      | ~ v1_funct_1(B_95)
      | ~ v5_relat_1(B_95,A_97)
      | ~ v1_relat_1(B_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_62,plain,(
    ~ r2_hidden(k1_funct_1('#skF_4','#skF_2'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_413,plain,
    ( ~ r2_hidden('#skF_2',k1_relat_1('#skF_4'))
    | ~ v1_funct_1('#skF_4')
    | ~ v5_relat_1('#skF_4','#skF_3')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_395,c_62])).

tff(c_426,plain,(
    ~ r2_hidden('#skF_2',k1_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_133,c_171,c_70,c_413])).

tff(c_436,plain,
    ( k11_relat_1('#skF_4','#skF_2') = k1_xboole_0
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_20,c_426])).

tff(c_442,plain,(
    k2_relat_1('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_133,c_207,c_436])).

tff(c_444,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_142,c_442])).

tff(c_445,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_140])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_458,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_445,c_2])).

tff(c_64,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_459,plain,(
    '#skF_3' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_445,c_64])).

tff(c_6,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_451,plain,(
    ! [A_3] : r1_tarski('#skF_4',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_445,c_6])).

tff(c_28,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_452,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_445,c_445,c_28])).

tff(c_581,plain,(
    ! [A_119,B_120] :
      ( r2_hidden(A_119,k1_relat_1(B_120))
      | k11_relat_1(B_120,A_119) = '#skF_4'
      | ~ v1_relat_1(B_120) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_445,c_20])).

tff(c_587,plain,(
    ! [A_119] :
      ( r2_hidden(A_119,'#skF_4')
      | k11_relat_1('#skF_4',A_119) = '#skF_4'
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_452,c_581])).

tff(c_591,plain,(
    ! [A_121] :
      ( r2_hidden(A_121,'#skF_4')
      | k11_relat_1('#skF_4',A_121) = '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_133,c_587])).

tff(c_52,plain,(
    ! [B_32,A_31] :
      ( ~ r1_tarski(B_32,A_31)
      | ~ r2_hidden(A_31,B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_594,plain,(
    ! [A_121] :
      ( ~ r1_tarski('#skF_4',A_121)
      | k11_relat_1('#skF_4',A_121) = '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_591,c_52])).

tff(c_597,plain,(
    ! [A_121] : k11_relat_1('#skF_4',A_121) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_451,c_594])).

tff(c_22,plain,(
    ! [B_17,A_16] :
      ( k11_relat_1(B_17,A_16) != k1_xboole_0
      | ~ r2_hidden(A_16,k1_relat_1(B_17))
      | ~ v1_relat_1(B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_599,plain,(
    ! [B_122,A_123] :
      ( k11_relat_1(B_122,A_123) != '#skF_4'
      | ~ r2_hidden(A_123,k1_relat_1(B_122))
      | ~ v1_relat_1(B_122) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_445,c_22])).

tff(c_609,plain,(
    ! [A_123] :
      ( k11_relat_1('#skF_4',A_123) != '#skF_4'
      | ~ r2_hidden(A_123,'#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_452,c_599])).

tff(c_613,plain,(
    ! [A_123] :
      ( k11_relat_1('#skF_4',A_123) != '#skF_4'
      | ~ r2_hidden(A_123,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_133,c_609])).

tff(c_624,plain,(
    ! [A_123] : ~ r2_hidden(A_123,'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_597,c_613])).

tff(c_40,plain,(
    ! [A_21,B_24] :
      ( k1_funct_1(A_21,B_24) = k1_xboole_0
      | r2_hidden(B_24,k1_relat_1(A_21))
      | ~ v1_funct_1(A_21)
      | ~ v1_relat_1(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_639,plain,(
    ! [A_128,B_129] :
      ( k1_funct_1(A_128,B_129) = '#skF_4'
      | r2_hidden(B_129,k1_relat_1(A_128))
      | ~ v1_funct_1(A_128)
      | ~ v1_relat_1(A_128) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_445,c_40])).

tff(c_648,plain,(
    ! [B_129] :
      ( k1_funct_1('#skF_4',B_129) = '#skF_4'
      | r2_hidden(B_129,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_452,c_639])).

tff(c_652,plain,(
    ! [B_129] :
      ( k1_funct_1('#skF_4',B_129) = '#skF_4'
      | r2_hidden(B_129,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_133,c_70,c_648])).

tff(c_653,plain,(
    ! [B_129] : k1_funct_1('#skF_4',B_129) = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_624,c_652])).

tff(c_654,plain,(
    ~ r2_hidden('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_653,c_62])).

tff(c_68,plain,(
    v1_funct_2('#skF_4',k1_tarski('#skF_2'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_4,plain,(
    ! [A_1] :
      ( r2_hidden('#skF_1'(A_1),A_1)
      | k1_xboole_0 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_450,plain,(
    ! [A_1] :
      ( r2_hidden('#skF_1'(A_1),A_1)
      | A_1 = '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_445,c_4])).

tff(c_60,plain,(
    ! [D_42,C_41,B_40,A_39] :
      ( r2_hidden(k1_funct_1(D_42,C_41),B_40)
      | k1_xboole_0 = B_40
      | ~ r2_hidden(C_41,A_39)
      | ~ m1_subset_1(D_42,k1_zfmisc_1(k2_zfmisc_1(A_39,B_40)))
      | ~ v1_funct_2(D_42,A_39,B_40)
      | ~ v1_funct_1(D_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_851,plain,(
    ! [D_158,C_159,B_160,A_161] :
      ( r2_hidden(k1_funct_1(D_158,C_159),B_160)
      | B_160 = '#skF_4'
      | ~ r2_hidden(C_159,A_161)
      | ~ m1_subset_1(D_158,k1_zfmisc_1(k2_zfmisc_1(A_161,B_160)))
      | ~ v1_funct_2(D_158,A_161,B_160)
      | ~ v1_funct_1(D_158) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_445,c_60])).

tff(c_965,plain,(
    ! [D_183,A_184,B_185] :
      ( r2_hidden(k1_funct_1(D_183,'#skF_1'(A_184)),B_185)
      | B_185 = '#skF_4'
      | ~ m1_subset_1(D_183,k1_zfmisc_1(k2_zfmisc_1(A_184,B_185)))
      | ~ v1_funct_2(D_183,A_184,B_185)
      | ~ v1_funct_1(D_183)
      | A_184 = '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_450,c_851])).

tff(c_993,plain,(
    ! [B_185,A_184] :
      ( r2_hidden('#skF_4',B_185)
      | B_185 = '#skF_4'
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_184,B_185)))
      | ~ v1_funct_2('#skF_4',A_184,B_185)
      | ~ v1_funct_1('#skF_4')
      | A_184 = '#skF_4' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_653,c_965])).

tff(c_1004,plain,(
    ! [B_186,A_187] :
      ( r2_hidden('#skF_4',B_186)
      | B_186 = '#skF_4'
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_187,B_186)))
      | ~ v1_funct_2('#skF_4',A_187,B_186)
      | A_187 = '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_993])).

tff(c_1007,plain,
    ( r2_hidden('#skF_4','#skF_3')
    | '#skF_3' = '#skF_4'
    | ~ v1_funct_2('#skF_4',k1_tarski('#skF_2'),'#skF_3')
    | k1_tarski('#skF_2') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_66,c_1004])).

tff(c_1010,plain,
    ( r2_hidden('#skF_4','#skF_3')
    | '#skF_3' = '#skF_4'
    | k1_tarski('#skF_2') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_1007])).

tff(c_1011,plain,(
    k1_tarski('#skF_2') = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_459,c_654,c_1010])).

tff(c_14,plain,(
    ! [A_10] : ~ v1_xboole_0(k1_tarski(A_10)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1022,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1011,c_14])).

tff(c_1027,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_458,c_1022])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 09:44:19 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.23/1.47  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.23/1.48  
% 3.23/1.48  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.23/1.48  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v5_ordinal1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k4_tarski > k2_zfmisc_1 > k2_tarski > k1_funct_1 > k11_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 3.23/1.48  
% 3.23/1.48  %Foreground sorts:
% 3.23/1.48  
% 3.23/1.48  
% 3.23/1.48  %Background operators:
% 3.23/1.48  
% 3.23/1.48  
% 3.23/1.48  %Foreground operators:
% 3.23/1.48  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.23/1.48  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.23/1.48  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.23/1.48  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.23/1.48  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.23/1.48  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.23/1.48  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.23/1.48  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.23/1.48  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.23/1.48  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.23/1.48  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.23/1.48  tff(v5_ordinal1, type, v5_ordinal1: $i > $o).
% 3.23/1.48  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.23/1.48  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.23/1.48  tff(k11_relat_1, type, k11_relat_1: ($i * $i) > $i).
% 3.23/1.48  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.23/1.48  tff('#skF_2', type, '#skF_2': $i).
% 3.23/1.48  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.23/1.48  tff('#skF_3', type, '#skF_3': $i).
% 3.23/1.48  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.23/1.48  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.23/1.48  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.23/1.48  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.23/1.48  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.23/1.48  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.23/1.48  tff('#skF_4', type, '#skF_4': $i).
% 3.23/1.48  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.23/1.48  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.23/1.48  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.23/1.48  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.23/1.48  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.23/1.48  
% 3.36/1.50  tff(f_154, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_tarski(A), B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => r2_hidden(k1_funct_1(C, A), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_funct_2)).
% 3.36/1.50  tff(f_124, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.36/1.50  tff(f_78, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_relat_1)).
% 3.36/1.50  tff(f_130, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.36/1.50  tff(f_67, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 3.36/1.50  tff(f_54, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 3.36/1.50  tff(f_50, axiom, (![A]: (v1_relat_1(A) => (![B]: (k11_relat_1(A, B) = k9_relat_1(A, k1_tarski(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d16_relat_1)).
% 3.36/1.50  tff(f_61, axiom, (![A, B]: (v1_relat_1(B) => (r2_hidden(A, k1_relat_1(B)) <=> ~(k11_relat_1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t205_relat_1)).
% 3.36/1.50  tff(f_107, axiom, (![A, B]: (((v1_relat_1(B) & v5_relat_1(B, A)) & v1_funct_1(B)) => (![C]: (r2_hidden(C, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, C), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t172_funct_1)).
% 3.36/1.50  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.36/1.50  tff(f_36, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.36/1.50  tff(f_70, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 3.36/1.50  tff(f_120, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 3.36/1.50  tff(f_96, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: ((r2_hidden(B, k1_relat_1(A)) => ((C = k1_funct_1(A, B)) <=> r2_hidden(k4_tarski(B, C), A))) & (~r2_hidden(B, k1_relat_1(A)) => ((C = k1_funct_1(A, B)) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_funct_1)).
% 3.36/1.50  tff(f_34, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 3.36/1.50  tff(f_142, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_funct_2)).
% 3.36/1.50  tff(f_45, axiom, (![A]: ~v1_xboole_0(k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_xboole_0)).
% 3.36/1.50  tff(c_66, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_2'), '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_154])).
% 3.36/1.50  tff(c_129, plain, (![C_55, A_56, B_57]: (v1_relat_1(C_55) | ~m1_subset_1(C_55, k1_zfmisc_1(k2_zfmisc_1(A_56, B_57))))), inference(cnfTransformation, [status(thm)], [f_124])).
% 3.36/1.50  tff(c_133, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_66, c_129])).
% 3.36/1.50  tff(c_30, plain, (![A_20]: (k2_relat_1(A_20)!=k1_xboole_0 | k1_xboole_0=A_20 | ~v1_relat_1(A_20))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.36/1.50  tff(c_140, plain, (k2_relat_1('#skF_4')!=k1_xboole_0 | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_133, c_30])).
% 3.36/1.50  tff(c_142, plain, (k2_relat_1('#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_140])).
% 3.36/1.50  tff(c_143, plain, (![C_58, A_59, B_60]: (v4_relat_1(C_58, A_59) | ~m1_subset_1(C_58, k1_zfmisc_1(k2_zfmisc_1(A_59, B_60))))), inference(cnfTransformation, [status(thm)], [f_130])).
% 3.36/1.50  tff(c_147, plain, (v4_relat_1('#skF_4', k1_tarski('#skF_2'))), inference(resolution, [status(thm)], [c_66, c_143])).
% 3.36/1.50  tff(c_172, plain, (![B_68, A_69]: (k7_relat_1(B_68, A_69)=B_68 | ~v4_relat_1(B_68, A_69) | ~v1_relat_1(B_68))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.36/1.50  tff(c_175, plain, (k7_relat_1('#skF_4', k1_tarski('#skF_2'))='#skF_4' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_147, c_172])).
% 3.36/1.50  tff(c_178, plain, (k7_relat_1('#skF_4', k1_tarski('#skF_2'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_133, c_175])).
% 3.36/1.50  tff(c_18, plain, (![B_15, A_14]: (k2_relat_1(k7_relat_1(B_15, A_14))=k9_relat_1(B_15, A_14) | ~v1_relat_1(B_15))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.36/1.50  tff(c_182, plain, (k9_relat_1('#skF_4', k1_tarski('#skF_2'))=k2_relat_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_178, c_18])).
% 3.36/1.50  tff(c_186, plain, (k9_relat_1('#skF_4', k1_tarski('#skF_2'))=k2_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_133, c_182])).
% 3.36/1.50  tff(c_16, plain, (![A_11, B_13]: (k9_relat_1(A_11, k1_tarski(B_13))=k11_relat_1(A_11, B_13) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.36/1.50  tff(c_200, plain, (k11_relat_1('#skF_4', '#skF_2')=k2_relat_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_186, c_16])).
% 3.36/1.50  tff(c_207, plain, (k11_relat_1('#skF_4', '#skF_2')=k2_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_133, c_200])).
% 3.36/1.50  tff(c_20, plain, (![A_16, B_17]: (r2_hidden(A_16, k1_relat_1(B_17)) | k11_relat_1(B_17, A_16)=k1_xboole_0 | ~v1_relat_1(B_17))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.36/1.50  tff(c_167, plain, (![C_65, B_66, A_67]: (v5_relat_1(C_65, B_66) | ~m1_subset_1(C_65, k1_zfmisc_1(k2_zfmisc_1(A_67, B_66))))), inference(cnfTransformation, [status(thm)], [f_130])).
% 3.36/1.50  tff(c_171, plain, (v5_relat_1('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_66, c_167])).
% 3.36/1.50  tff(c_70, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_154])).
% 3.36/1.50  tff(c_395, plain, (![B_95, C_96, A_97]: (r2_hidden(k1_funct_1(B_95, C_96), A_97) | ~r2_hidden(C_96, k1_relat_1(B_95)) | ~v1_funct_1(B_95) | ~v5_relat_1(B_95, A_97) | ~v1_relat_1(B_95))), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.36/1.50  tff(c_62, plain, (~r2_hidden(k1_funct_1('#skF_4', '#skF_2'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_154])).
% 3.36/1.50  tff(c_413, plain, (~r2_hidden('#skF_2', k1_relat_1('#skF_4')) | ~v1_funct_1('#skF_4') | ~v5_relat_1('#skF_4', '#skF_3') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_395, c_62])).
% 3.36/1.50  tff(c_426, plain, (~r2_hidden('#skF_2', k1_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_133, c_171, c_70, c_413])).
% 3.36/1.50  tff(c_436, plain, (k11_relat_1('#skF_4', '#skF_2')=k1_xboole_0 | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_20, c_426])).
% 3.36/1.50  tff(c_442, plain, (k2_relat_1('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_133, c_207, c_436])).
% 3.36/1.50  tff(c_444, plain, $false, inference(negUnitSimplification, [status(thm)], [c_142, c_442])).
% 3.36/1.50  tff(c_445, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_140])).
% 3.36/1.50  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 3.36/1.50  tff(c_458, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_445, c_2])).
% 3.36/1.50  tff(c_64, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_154])).
% 3.36/1.50  tff(c_459, plain, ('#skF_3'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_445, c_64])).
% 3.36/1.50  tff(c_6, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.36/1.50  tff(c_451, plain, (![A_3]: (r1_tarski('#skF_4', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_445, c_6])).
% 3.36/1.50  tff(c_28, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.36/1.50  tff(c_452, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_445, c_445, c_28])).
% 3.36/1.50  tff(c_581, plain, (![A_119, B_120]: (r2_hidden(A_119, k1_relat_1(B_120)) | k11_relat_1(B_120, A_119)='#skF_4' | ~v1_relat_1(B_120))), inference(demodulation, [status(thm), theory('equality')], [c_445, c_20])).
% 3.36/1.50  tff(c_587, plain, (![A_119]: (r2_hidden(A_119, '#skF_4') | k11_relat_1('#skF_4', A_119)='#skF_4' | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_452, c_581])).
% 3.36/1.50  tff(c_591, plain, (![A_121]: (r2_hidden(A_121, '#skF_4') | k11_relat_1('#skF_4', A_121)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_133, c_587])).
% 3.36/1.50  tff(c_52, plain, (![B_32, A_31]: (~r1_tarski(B_32, A_31) | ~r2_hidden(A_31, B_32))), inference(cnfTransformation, [status(thm)], [f_120])).
% 3.36/1.50  tff(c_594, plain, (![A_121]: (~r1_tarski('#skF_4', A_121) | k11_relat_1('#skF_4', A_121)='#skF_4')), inference(resolution, [status(thm)], [c_591, c_52])).
% 3.36/1.50  tff(c_597, plain, (![A_121]: (k11_relat_1('#skF_4', A_121)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_451, c_594])).
% 3.36/1.50  tff(c_22, plain, (![B_17, A_16]: (k11_relat_1(B_17, A_16)!=k1_xboole_0 | ~r2_hidden(A_16, k1_relat_1(B_17)) | ~v1_relat_1(B_17))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.36/1.50  tff(c_599, plain, (![B_122, A_123]: (k11_relat_1(B_122, A_123)!='#skF_4' | ~r2_hidden(A_123, k1_relat_1(B_122)) | ~v1_relat_1(B_122))), inference(demodulation, [status(thm), theory('equality')], [c_445, c_22])).
% 3.36/1.50  tff(c_609, plain, (![A_123]: (k11_relat_1('#skF_4', A_123)!='#skF_4' | ~r2_hidden(A_123, '#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_452, c_599])).
% 3.36/1.50  tff(c_613, plain, (![A_123]: (k11_relat_1('#skF_4', A_123)!='#skF_4' | ~r2_hidden(A_123, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_133, c_609])).
% 3.36/1.50  tff(c_624, plain, (![A_123]: (~r2_hidden(A_123, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_597, c_613])).
% 3.36/1.50  tff(c_40, plain, (![A_21, B_24]: (k1_funct_1(A_21, B_24)=k1_xboole_0 | r2_hidden(B_24, k1_relat_1(A_21)) | ~v1_funct_1(A_21) | ~v1_relat_1(A_21))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.36/1.50  tff(c_639, plain, (![A_128, B_129]: (k1_funct_1(A_128, B_129)='#skF_4' | r2_hidden(B_129, k1_relat_1(A_128)) | ~v1_funct_1(A_128) | ~v1_relat_1(A_128))), inference(demodulation, [status(thm), theory('equality')], [c_445, c_40])).
% 3.36/1.50  tff(c_648, plain, (![B_129]: (k1_funct_1('#skF_4', B_129)='#skF_4' | r2_hidden(B_129, '#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_452, c_639])).
% 3.36/1.50  tff(c_652, plain, (![B_129]: (k1_funct_1('#skF_4', B_129)='#skF_4' | r2_hidden(B_129, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_133, c_70, c_648])).
% 3.36/1.50  tff(c_653, plain, (![B_129]: (k1_funct_1('#skF_4', B_129)='#skF_4')), inference(negUnitSimplification, [status(thm)], [c_624, c_652])).
% 3.36/1.50  tff(c_654, plain, (~r2_hidden('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_653, c_62])).
% 3.36/1.50  tff(c_68, plain, (v1_funct_2('#skF_4', k1_tarski('#skF_2'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_154])).
% 3.36/1.50  tff(c_4, plain, (![A_1]: (r2_hidden('#skF_1'(A_1), A_1) | k1_xboole_0=A_1)), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.36/1.50  tff(c_450, plain, (![A_1]: (r2_hidden('#skF_1'(A_1), A_1) | A_1='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_445, c_4])).
% 3.36/1.50  tff(c_60, plain, (![D_42, C_41, B_40, A_39]: (r2_hidden(k1_funct_1(D_42, C_41), B_40) | k1_xboole_0=B_40 | ~r2_hidden(C_41, A_39) | ~m1_subset_1(D_42, k1_zfmisc_1(k2_zfmisc_1(A_39, B_40))) | ~v1_funct_2(D_42, A_39, B_40) | ~v1_funct_1(D_42))), inference(cnfTransformation, [status(thm)], [f_142])).
% 3.36/1.50  tff(c_851, plain, (![D_158, C_159, B_160, A_161]: (r2_hidden(k1_funct_1(D_158, C_159), B_160) | B_160='#skF_4' | ~r2_hidden(C_159, A_161) | ~m1_subset_1(D_158, k1_zfmisc_1(k2_zfmisc_1(A_161, B_160))) | ~v1_funct_2(D_158, A_161, B_160) | ~v1_funct_1(D_158))), inference(demodulation, [status(thm), theory('equality')], [c_445, c_60])).
% 3.36/1.50  tff(c_965, plain, (![D_183, A_184, B_185]: (r2_hidden(k1_funct_1(D_183, '#skF_1'(A_184)), B_185) | B_185='#skF_4' | ~m1_subset_1(D_183, k1_zfmisc_1(k2_zfmisc_1(A_184, B_185))) | ~v1_funct_2(D_183, A_184, B_185) | ~v1_funct_1(D_183) | A_184='#skF_4')), inference(resolution, [status(thm)], [c_450, c_851])).
% 3.36/1.50  tff(c_993, plain, (![B_185, A_184]: (r2_hidden('#skF_4', B_185) | B_185='#skF_4' | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_184, B_185))) | ~v1_funct_2('#skF_4', A_184, B_185) | ~v1_funct_1('#skF_4') | A_184='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_653, c_965])).
% 3.36/1.50  tff(c_1004, plain, (![B_186, A_187]: (r2_hidden('#skF_4', B_186) | B_186='#skF_4' | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_187, B_186))) | ~v1_funct_2('#skF_4', A_187, B_186) | A_187='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_993])).
% 3.36/1.50  tff(c_1007, plain, (r2_hidden('#skF_4', '#skF_3') | '#skF_3'='#skF_4' | ~v1_funct_2('#skF_4', k1_tarski('#skF_2'), '#skF_3') | k1_tarski('#skF_2')='#skF_4'), inference(resolution, [status(thm)], [c_66, c_1004])).
% 3.36/1.50  tff(c_1010, plain, (r2_hidden('#skF_4', '#skF_3') | '#skF_3'='#skF_4' | k1_tarski('#skF_2')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_1007])).
% 3.36/1.50  tff(c_1011, plain, (k1_tarski('#skF_2')='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_459, c_654, c_1010])).
% 3.36/1.50  tff(c_14, plain, (![A_10]: (~v1_xboole_0(k1_tarski(A_10)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.36/1.50  tff(c_1022, plain, (~v1_xboole_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1011, c_14])).
% 3.36/1.50  tff(c_1027, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_458, c_1022])).
% 3.36/1.50  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.36/1.50  
% 3.36/1.50  Inference rules
% 3.36/1.50  ----------------------
% 3.36/1.50  #Ref     : 0
% 3.36/1.50  #Sup     : 189
% 3.36/1.50  #Fact    : 0
% 3.36/1.50  #Define  : 0
% 3.36/1.50  #Split   : 3
% 3.36/1.50  #Chain   : 0
% 3.36/1.50  #Close   : 0
% 3.36/1.50  
% 3.36/1.50  Ordering : KBO
% 3.36/1.50  
% 3.36/1.50  Simplification rules
% 3.36/1.50  ----------------------
% 3.36/1.50  #Subsume      : 27
% 3.36/1.50  #Demod        : 231
% 3.36/1.50  #Tautology    : 91
% 3.36/1.50  #SimpNegUnit  : 7
% 3.36/1.50  #BackRed      : 19
% 3.36/1.50  
% 3.36/1.50  #Partial instantiations: 0
% 3.36/1.50  #Strategies tried      : 1
% 3.36/1.50  
% 3.36/1.50  Timing (in seconds)
% 3.36/1.50  ----------------------
% 3.36/1.50  Preprocessing        : 0.35
% 3.36/1.50  Parsing              : 0.19
% 3.36/1.51  CNF conversion       : 0.02
% 3.36/1.51  Main loop            : 0.38
% 3.36/1.51  Inferencing          : 0.14
% 3.36/1.51  Reduction            : 0.12
% 3.36/1.51  Demodulation         : 0.08
% 3.36/1.51  BG Simplification    : 0.02
% 3.36/1.51  Subsumption          : 0.07
% 3.36/1.51  Abstraction          : 0.02
% 3.36/1.51  MUC search           : 0.00
% 3.36/1.51  Cooper               : 0.00
% 3.36/1.51  Total                : 0.77
% 3.36/1.51  Index Insertion      : 0.00
% 3.36/1.51  Index Deletion       : 0.00
% 3.36/1.51  Index Matching       : 0.00
% 3.36/1.51  BG Taut test         : 0.00
%------------------------------------------------------------------------------
