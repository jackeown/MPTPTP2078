%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:21 EST 2020

% Result     : Theorem 5.64s
% Output     : CNFRefutation 5.84s
% Verified   : 
% Statistics : Number of formulae       :  121 ( 627 expanded)
%              Number of leaves         :   34 ( 232 expanded)
%              Depth                    :   24
%              Number of atoms          :  251 (2052 expanded)
%              Number of equality atoms :   43 ( 474 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_97,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( ! [D] :
              ~ ( r2_hidden(D,B)
                & ! [E] :
                    ~ ( r2_hidden(E,A)
                      & D = k1_funct_1(C,E) ) )
         => k2_relset_1(A,B,C) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_funct_2)).

tff(f_56,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_47,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_78,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_hidden(C,A)
       => ( B = k1_xboole_0
          | r2_hidden(k1_funct_1(D,C),k2_relset_1(A,B,D)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_funct_2)).

tff(f_41,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
        <=> r2_hidden(C,B) )
     => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tarski)).

tff(c_36,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_53,plain,(
    ! [C_37,A_38,B_39] :
      ( v1_relat_1(C_37)
      | ~ m1_subset_1(C_37,k1_zfmisc_1(k2_zfmisc_1(A_38,B_39))) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_57,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_36,c_53])).

tff(c_118,plain,(
    ! [C_58,B_59,A_60] :
      ( v5_relat_1(C_58,B_59)
      | ~ m1_subset_1(C_58,k1_zfmisc_1(k2_zfmisc_1(A_60,B_59))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_122,plain,(
    v5_relat_1('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_36,c_118])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_72,plain,(
    ! [A_43,B_44] :
      ( ~ r2_hidden('#skF_1'(A_43,B_44),B_44)
      | r1_tarski(A_43,B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_77,plain,(
    ! [A_1] : r1_tarski(A_1,A_1) ),
    inference(resolution,[status(thm)],[c_6,c_72])).

tff(c_20,plain,(
    ! [B_11,A_10] :
      ( r1_tarski(k2_relat_1(B_11),A_10)
      | ~ v5_relat_1(B_11,A_10)
      | ~ v1_relat_1(B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_103,plain,(
    ! [C_53,B_54,A_55] :
      ( r2_hidden(C_53,B_54)
      | ~ r2_hidden(C_53,A_55)
      | ~ r1_tarski(A_55,B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_146,plain,(
    ! [A_68,B_69,B_70] :
      ( r2_hidden('#skF_1'(A_68,B_69),B_70)
      | ~ r1_tarski(A_68,B_70)
      | r1_tarski(A_68,B_69) ) ),
    inference(resolution,[status(thm)],[c_6,c_103])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1595,plain,(
    ! [A_215,B_216,B_217,B_218] :
      ( r2_hidden('#skF_1'(A_215,B_216),B_217)
      | ~ r1_tarski(B_218,B_217)
      | ~ r1_tarski(A_215,B_218)
      | r1_tarski(A_215,B_216) ) ),
    inference(resolution,[status(thm)],[c_146,c_2])).

tff(c_3551,plain,(
    ! [A_432,B_433,A_434,B_435] :
      ( r2_hidden('#skF_1'(A_432,B_433),A_434)
      | ~ r1_tarski(A_432,k2_relat_1(B_435))
      | r1_tarski(A_432,B_433)
      | ~ v5_relat_1(B_435,A_434)
      | ~ v1_relat_1(B_435) ) ),
    inference(resolution,[status(thm)],[c_20,c_1595])).

tff(c_3579,plain,(
    ! [B_436,B_437,A_438] :
      ( r2_hidden('#skF_1'(k2_relat_1(B_436),B_437),A_438)
      | r1_tarski(k2_relat_1(B_436),B_437)
      | ~ v5_relat_1(B_436,A_438)
      | ~ v1_relat_1(B_436) ) ),
    inference(resolution,[status(thm)],[c_77,c_3551])).

tff(c_265,plain,(
    ! [A_89,B_90,C_91] :
      ( k2_relset_1(A_89,B_90,C_91) = k2_relat_1(C_91)
      | ~ m1_subset_1(C_91,k1_zfmisc_1(k2_zfmisc_1(A_89,B_90))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_269,plain,(
    k2_relset_1('#skF_4','#skF_5','#skF_6') = k2_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_36,c_265])).

tff(c_34,plain,(
    k2_relset_1('#skF_4','#skF_5','#skF_6') != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_270,plain,(
    k2_relat_1('#skF_6') != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_269,c_34])).

tff(c_40,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_38,plain,(
    v1_funct_2('#skF_6','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_333,plain,(
    ! [D_99,C_100,A_101,B_102] :
      ( r2_hidden(k1_funct_1(D_99,C_100),k2_relset_1(A_101,B_102,D_99))
      | k1_xboole_0 = B_102
      | ~ r2_hidden(C_100,A_101)
      | ~ m1_subset_1(D_99,k1_zfmisc_1(k2_zfmisc_1(A_101,B_102)))
      | ~ v1_funct_2(D_99,A_101,B_102)
      | ~ v1_funct_1(D_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_341,plain,(
    ! [C_100] :
      ( r2_hidden(k1_funct_1('#skF_6',C_100),k2_relat_1('#skF_6'))
      | k1_xboole_0 = '#skF_5'
      | ~ r2_hidden(C_100,'#skF_4')
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5')))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_5')
      | ~ v1_funct_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_269,c_333])).

tff(c_348,plain,(
    ! [C_100] :
      ( r2_hidden(k1_funct_1('#skF_6',C_100),k2_relat_1('#skF_6'))
      | k1_xboole_0 = '#skF_5'
      | ~ r2_hidden(C_100,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_36,c_341])).

tff(c_421,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_348])).

tff(c_16,plain,(
    ! [A_9] : r1_tarski(k1_xboole_0,A_9) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_22,plain,(
    ! [B_13,A_12] :
      ( ~ r1_tarski(B_13,A_12)
      | ~ r2_hidden(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_169,plain,(
    ! [B_74,A_75,B_76] :
      ( ~ r1_tarski(B_74,'#skF_1'(A_75,B_76))
      | ~ r1_tarski(A_75,B_74)
      | r1_tarski(A_75,B_76) ) ),
    inference(resolution,[status(thm)],[c_146,c_22])).

tff(c_185,plain,(
    ! [A_77,B_78] :
      ( ~ r1_tarski(A_77,k1_xboole_0)
      | r1_tarski(A_77,B_78) ) ),
    inference(resolution,[status(thm)],[c_16,c_169])).

tff(c_195,plain,(
    ! [B_11,B_78] :
      ( r1_tarski(k2_relat_1(B_11),B_78)
      | ~ v5_relat_1(B_11,k1_xboole_0)
      | ~ v1_relat_1(B_11) ) ),
    inference(resolution,[status(thm)],[c_20,c_185])).

tff(c_243,plain,(
    ! [A_87,B_88] :
      ( r2_hidden('#skF_2'(A_87,B_88),B_88)
      | r2_hidden('#skF_3'(A_87,B_88),A_87)
      | B_88 = A_87 ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_275,plain,(
    ! [B_92,A_93] :
      ( ~ r1_tarski(B_92,'#skF_2'(A_93,B_92))
      | r2_hidden('#skF_3'(A_93,B_92),A_93)
      | B_92 = A_93 ) ),
    inference(resolution,[status(thm)],[c_243,c_22])).

tff(c_288,plain,(
    ! [A_94] :
      ( r2_hidden('#skF_3'(A_94,k1_xboole_0),A_94)
      | k1_xboole_0 = A_94 ) ),
    inference(resolution,[status(thm)],[c_16,c_275])).

tff(c_302,plain,(
    ! [A_95] :
      ( ~ r1_tarski(A_95,'#skF_3'(A_95,k1_xboole_0))
      | k1_xboole_0 = A_95 ) ),
    inference(resolution,[status(thm)],[c_288,c_22])).

tff(c_315,plain,(
    ! [B_11] :
      ( k2_relat_1(B_11) = k1_xboole_0
      | ~ v5_relat_1(B_11,k1_xboole_0)
      | ~ v1_relat_1(B_11) ) ),
    inference(resolution,[status(thm)],[c_195,c_302])).

tff(c_575,plain,(
    ! [B_124] :
      ( k2_relat_1(B_124) = '#skF_5'
      | ~ v5_relat_1(B_124,'#skF_5')
      | ~ v1_relat_1(B_124) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_421,c_421,c_315])).

tff(c_578,plain,
    ( k2_relat_1('#skF_6') = '#skF_5'
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_122,c_575])).

tff(c_581,plain,(
    k2_relat_1('#skF_6') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_57,c_578])).

tff(c_583,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_270,c_581])).

tff(c_585,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_348])).

tff(c_44,plain,(
    ! [D_30] :
      ( r2_hidden('#skF_7'(D_30),'#skF_4')
      | ~ r2_hidden(D_30,'#skF_5') ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_42,plain,(
    ! [D_30] :
      ( k1_funct_1('#skF_6','#skF_7'(D_30)) = D_30
      | ~ r2_hidden(D_30,'#skF_5') ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_344,plain,(
    ! [D_30,A_101,B_102] :
      ( r2_hidden(D_30,k2_relset_1(A_101,B_102,'#skF_6'))
      | k1_xboole_0 = B_102
      | ~ r2_hidden('#skF_7'(D_30),A_101)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(A_101,B_102)))
      | ~ v1_funct_2('#skF_6',A_101,B_102)
      | ~ v1_funct_1('#skF_6')
      | ~ r2_hidden(D_30,'#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_333])).

tff(c_414,plain,(
    ! [D_107,A_108,B_109] :
      ( r2_hidden(D_107,k2_relset_1(A_108,B_109,'#skF_6'))
      | k1_xboole_0 = B_109
      | ~ r2_hidden('#skF_7'(D_107),A_108)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(A_108,B_109)))
      | ~ v1_funct_2('#skF_6',A_108,B_109)
      | ~ r2_hidden(D_107,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_344])).

tff(c_586,plain,(
    ! [D_125,B_126] :
      ( r2_hidden(D_125,k2_relset_1('#skF_4',B_126,'#skF_6'))
      | k1_xboole_0 = B_126
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4',B_126)))
      | ~ v1_funct_2('#skF_6','#skF_4',B_126)
      | ~ r2_hidden(D_125,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_44,c_414])).

tff(c_588,plain,(
    ! [D_125] :
      ( r2_hidden(D_125,k2_relset_1('#skF_4','#skF_5','#skF_6'))
      | k1_xboole_0 = '#skF_5'
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_5')
      | ~ r2_hidden(D_125,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_36,c_586])).

tff(c_591,plain,(
    ! [D_125] :
      ( r2_hidden(D_125,k2_relat_1('#skF_6'))
      | k1_xboole_0 = '#skF_5'
      | ~ r2_hidden(D_125,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_269,c_588])).

tff(c_604,plain,(
    ! [D_128] :
      ( r2_hidden(D_128,k2_relat_1('#skF_6'))
      | ~ r2_hidden(D_128,'#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_585,c_591])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_628,plain,(
    ! [A_1] :
      ( r1_tarski(A_1,k2_relat_1('#skF_6'))
      | ~ r2_hidden('#skF_1'(A_1,k2_relat_1('#skF_6')),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_604,c_4])).

tff(c_3601,plain,(
    ! [B_439] :
      ( r1_tarski(k2_relat_1(B_439),k2_relat_1('#skF_6'))
      | ~ v5_relat_1(B_439,'#skF_5')
      | ~ v1_relat_1(B_439) ) ),
    inference(resolution,[status(thm)],[c_3579,c_628])).

tff(c_18,plain,(
    ! [B_11,A_10] :
      ( v5_relat_1(B_11,A_10)
      | ~ r1_tarski(k2_relat_1(B_11),A_10)
      | ~ v1_relat_1(B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_3739,plain,(
    ! [B_439] :
      ( v5_relat_1(B_439,k2_relat_1('#skF_6'))
      | ~ v5_relat_1(B_439,'#skF_5')
      | ~ v1_relat_1(B_439) ) ),
    inference(resolution,[status(thm)],[c_3601,c_18])).

tff(c_761,plain,(
    ! [A_141] :
      ( r1_tarski(A_141,k2_relat_1('#skF_6'))
      | ~ r2_hidden('#skF_1'(A_141,k2_relat_1('#skF_6')),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_604,c_4])).

tff(c_771,plain,(
    r1_tarski('#skF_5',k2_relat_1('#skF_6')) ),
    inference(resolution,[status(thm)],[c_6,c_761])).

tff(c_1153,plain,(
    ! [A_173,B_174,B_175] :
      ( r2_hidden('#skF_3'(A_173,B_174),B_175)
      | ~ r1_tarski(A_173,B_175)
      | r2_hidden('#skF_2'(A_173,B_174),B_174)
      | B_174 = A_173 ) ),
    inference(resolution,[status(thm)],[c_243,c_2])).

tff(c_10,plain,(
    ! [A_6,B_7] :
      ( r2_hidden('#skF_2'(A_6,B_7),B_7)
      | ~ r2_hidden('#skF_3'(A_6,B_7),B_7)
      | B_7 = A_6 ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1270,plain,(
    ! [A_179,B_180] :
      ( ~ r1_tarski(A_179,B_180)
      | r2_hidden('#skF_2'(A_179,B_180),B_180)
      | B_180 = A_179 ) ),
    inference(resolution,[status(thm)],[c_1153,c_10])).

tff(c_1302,plain,(
    ! [A_179,B_180,B_2] :
      ( r2_hidden('#skF_2'(A_179,B_180),B_2)
      | ~ r1_tarski(B_180,B_2)
      | ~ r1_tarski(A_179,B_180)
      | B_180 = A_179 ) ),
    inference(resolution,[status(thm)],[c_1270,c_2])).

tff(c_12,plain,(
    ! [A_6,B_7] :
      ( ~ r2_hidden('#skF_2'(A_6,B_7),A_6)
      | r2_hidden('#skF_3'(A_6,B_7),A_6)
      | B_7 = A_6 ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_603,plain,(
    ! [D_125] :
      ( r2_hidden(D_125,k2_relat_1('#skF_6'))
      | ~ r2_hidden(D_125,'#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_585,c_591])).

tff(c_14,plain,(
    ! [A_6,B_7] :
      ( r2_hidden('#skF_2'(A_6,B_7),B_7)
      | r2_hidden('#skF_3'(A_6,B_7),A_6)
      | B_7 = A_6 ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_817,plain,(
    ! [D_148,B_149] :
      ( r2_hidden(D_148,B_149)
      | ~ r1_tarski(k2_relat_1('#skF_6'),B_149)
      | ~ r2_hidden(D_148,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_604,c_2])).

tff(c_826,plain,(
    ! [D_148,A_10] :
      ( r2_hidden(D_148,A_10)
      | ~ r2_hidden(D_148,'#skF_5')
      | ~ v5_relat_1('#skF_6',A_10)
      | ~ v1_relat_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_20,c_817])).

tff(c_838,plain,(
    ! [D_150,A_151] :
      ( r2_hidden(D_150,A_151)
      | ~ r2_hidden(D_150,'#skF_5')
      | ~ v5_relat_1('#skF_6',A_151) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_57,c_826])).

tff(c_3850,plain,(
    ! [B_448,A_449] :
      ( r2_hidden('#skF_3'('#skF_5',B_448),A_449)
      | ~ v5_relat_1('#skF_6',A_449)
      | r2_hidden('#skF_2'('#skF_5',B_448),B_448)
      | B_448 = '#skF_5' ) ),
    inference(resolution,[status(thm)],[c_14,c_838])).

tff(c_3901,plain,(
    ! [A_450] :
      ( ~ v5_relat_1('#skF_6',A_450)
      | r2_hidden('#skF_2'('#skF_5',A_450),A_450)
      | A_450 = '#skF_5' ) ),
    inference(resolution,[status(thm)],[c_3850,c_10])).

tff(c_3972,plain,(
    ! [A_456,B_457] :
      ( r2_hidden('#skF_2'('#skF_5',A_456),B_457)
      | ~ r1_tarski(A_456,B_457)
      | ~ v5_relat_1('#skF_6',A_456)
      | A_456 = '#skF_5' ) ),
    inference(resolution,[status(thm)],[c_3901,c_2])).

tff(c_8,plain,(
    ! [A_6,B_7] :
      ( ~ r2_hidden('#skF_2'(A_6,B_7),A_6)
      | ~ r2_hidden('#skF_3'(A_6,B_7),B_7)
      | B_7 = A_6 ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_4007,plain,(
    ! [A_460] :
      ( ~ r2_hidden('#skF_3'('#skF_5',A_460),A_460)
      | ~ r1_tarski(A_460,'#skF_5')
      | ~ v5_relat_1('#skF_6',A_460)
      | A_460 = '#skF_5' ) ),
    inference(resolution,[status(thm)],[c_3972,c_8])).

tff(c_4055,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_6'),'#skF_5')
    | ~ v5_relat_1('#skF_6',k2_relat_1('#skF_6'))
    | k2_relat_1('#skF_6') = '#skF_5'
    | ~ r2_hidden('#skF_3'('#skF_5',k2_relat_1('#skF_6')),'#skF_5') ),
    inference(resolution,[status(thm)],[c_603,c_4007])).

tff(c_4098,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_6'),'#skF_5')
    | ~ v5_relat_1('#skF_6',k2_relat_1('#skF_6'))
    | ~ r2_hidden('#skF_3'('#skF_5',k2_relat_1('#skF_6')),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_270,c_4055])).

tff(c_4287,plain,(
    ~ r2_hidden('#skF_3'('#skF_5',k2_relat_1('#skF_6')),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_4098])).

tff(c_4311,plain,
    ( ~ r2_hidden('#skF_2'('#skF_5',k2_relat_1('#skF_6')),'#skF_5')
    | k2_relat_1('#skF_6') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_12,c_4287])).

tff(c_4335,plain,(
    ~ r2_hidden('#skF_2'('#skF_5',k2_relat_1('#skF_6')),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_270,c_4311])).

tff(c_4345,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_6'),'#skF_5')
    | ~ r1_tarski('#skF_5',k2_relat_1('#skF_6'))
    | k2_relat_1('#skF_6') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_1302,c_4335])).

tff(c_4354,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_6'),'#skF_5')
    | k2_relat_1('#skF_6') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_771,c_4345])).

tff(c_4355,plain,(
    ~ r1_tarski(k2_relat_1('#skF_6'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_270,c_4354])).

tff(c_4361,plain,
    ( ~ v5_relat_1('#skF_6','#skF_5')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_20,c_4355])).

tff(c_4368,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_57,c_122,c_4361])).

tff(c_4369,plain,
    ( ~ v5_relat_1('#skF_6',k2_relat_1('#skF_6'))
    | ~ r1_tarski(k2_relat_1('#skF_6'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_4098])).

tff(c_4381,plain,(
    ~ r1_tarski(k2_relat_1('#skF_6'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_4369])).

tff(c_4387,plain,
    ( ~ v5_relat_1('#skF_6','#skF_5')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_20,c_4381])).

tff(c_4394,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_57,c_122,c_4387])).

tff(c_4395,plain,(
    ~ v5_relat_1('#skF_6',k2_relat_1('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_4369])).

tff(c_4399,plain,
    ( ~ v5_relat_1('#skF_6','#skF_5')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_3739,c_4395])).

tff(c_4409,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_57,c_122,c_4399])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n016.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 12:47:34 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.64/2.08  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.64/2.09  
% 5.64/2.09  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.64/2.09  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2 > #skF_1
% 5.64/2.09  
% 5.64/2.09  %Foreground sorts:
% 5.64/2.09  
% 5.64/2.09  
% 5.64/2.09  %Background operators:
% 5.64/2.09  
% 5.64/2.09  
% 5.64/2.09  %Foreground operators:
% 5.64/2.09  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 5.64/2.09  tff('#skF_7', type, '#skF_7': $i > $i).
% 5.64/2.09  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.64/2.09  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.64/2.09  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.64/2.09  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.64/2.09  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 5.64/2.09  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.64/2.09  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.64/2.09  tff('#skF_5', type, '#skF_5': $i).
% 5.64/2.09  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.64/2.09  tff('#skF_6', type, '#skF_6': $i).
% 5.64/2.09  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 5.64/2.09  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.64/2.09  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 5.64/2.09  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.64/2.09  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.64/2.09  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.64/2.09  tff('#skF_4', type, '#skF_4': $i).
% 5.64/2.09  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.64/2.09  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 5.64/2.09  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 5.64/2.09  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.64/2.09  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.64/2.09  
% 5.84/2.11  tff(f_97, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((![D]: ~(r2_hidden(D, B) & (![E]: ~(r2_hidden(E, A) & (D = k1_funct_1(C, E)))))) => (k2_relset_1(A, B, C) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_funct_2)).
% 5.84/2.11  tff(f_56, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 5.84/2.11  tff(f_62, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 5.84/2.11  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 5.84/2.11  tff(f_47, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 5.84/2.11  tff(f_66, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 5.84/2.11  tff(f_78, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), k2_relset_1(A, B, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_funct_2)).
% 5.84/2.11  tff(f_41, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 5.84/2.11  tff(f_52, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 5.84/2.11  tff(f_39, axiom, (![A, B]: ((![C]: (r2_hidden(C, A) <=> r2_hidden(C, B))) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tarski)).
% 5.84/2.11  tff(c_36, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_97])).
% 5.84/2.11  tff(c_53, plain, (![C_37, A_38, B_39]: (v1_relat_1(C_37) | ~m1_subset_1(C_37, k1_zfmisc_1(k2_zfmisc_1(A_38, B_39))))), inference(cnfTransformation, [status(thm)], [f_56])).
% 5.84/2.11  tff(c_57, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_36, c_53])).
% 5.84/2.11  tff(c_118, plain, (![C_58, B_59, A_60]: (v5_relat_1(C_58, B_59) | ~m1_subset_1(C_58, k1_zfmisc_1(k2_zfmisc_1(A_60, B_59))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 5.84/2.11  tff(c_122, plain, (v5_relat_1('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_36, c_118])).
% 5.84/2.11  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.84/2.11  tff(c_72, plain, (![A_43, B_44]: (~r2_hidden('#skF_1'(A_43, B_44), B_44) | r1_tarski(A_43, B_44))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.84/2.11  tff(c_77, plain, (![A_1]: (r1_tarski(A_1, A_1))), inference(resolution, [status(thm)], [c_6, c_72])).
% 5.84/2.11  tff(c_20, plain, (![B_11, A_10]: (r1_tarski(k2_relat_1(B_11), A_10) | ~v5_relat_1(B_11, A_10) | ~v1_relat_1(B_11))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.84/2.11  tff(c_103, plain, (![C_53, B_54, A_55]: (r2_hidden(C_53, B_54) | ~r2_hidden(C_53, A_55) | ~r1_tarski(A_55, B_54))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.84/2.11  tff(c_146, plain, (![A_68, B_69, B_70]: (r2_hidden('#skF_1'(A_68, B_69), B_70) | ~r1_tarski(A_68, B_70) | r1_tarski(A_68, B_69))), inference(resolution, [status(thm)], [c_6, c_103])).
% 5.84/2.11  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.84/2.11  tff(c_1595, plain, (![A_215, B_216, B_217, B_218]: (r2_hidden('#skF_1'(A_215, B_216), B_217) | ~r1_tarski(B_218, B_217) | ~r1_tarski(A_215, B_218) | r1_tarski(A_215, B_216))), inference(resolution, [status(thm)], [c_146, c_2])).
% 5.84/2.11  tff(c_3551, plain, (![A_432, B_433, A_434, B_435]: (r2_hidden('#skF_1'(A_432, B_433), A_434) | ~r1_tarski(A_432, k2_relat_1(B_435)) | r1_tarski(A_432, B_433) | ~v5_relat_1(B_435, A_434) | ~v1_relat_1(B_435))), inference(resolution, [status(thm)], [c_20, c_1595])).
% 5.84/2.11  tff(c_3579, plain, (![B_436, B_437, A_438]: (r2_hidden('#skF_1'(k2_relat_1(B_436), B_437), A_438) | r1_tarski(k2_relat_1(B_436), B_437) | ~v5_relat_1(B_436, A_438) | ~v1_relat_1(B_436))), inference(resolution, [status(thm)], [c_77, c_3551])).
% 5.84/2.11  tff(c_265, plain, (![A_89, B_90, C_91]: (k2_relset_1(A_89, B_90, C_91)=k2_relat_1(C_91) | ~m1_subset_1(C_91, k1_zfmisc_1(k2_zfmisc_1(A_89, B_90))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 5.84/2.11  tff(c_269, plain, (k2_relset_1('#skF_4', '#skF_5', '#skF_6')=k2_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_36, c_265])).
% 5.84/2.11  tff(c_34, plain, (k2_relset_1('#skF_4', '#skF_5', '#skF_6')!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_97])).
% 5.84/2.11  tff(c_270, plain, (k2_relat_1('#skF_6')!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_269, c_34])).
% 5.84/2.11  tff(c_40, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_97])).
% 5.84/2.11  tff(c_38, plain, (v1_funct_2('#skF_6', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_97])).
% 5.84/2.11  tff(c_333, plain, (![D_99, C_100, A_101, B_102]: (r2_hidden(k1_funct_1(D_99, C_100), k2_relset_1(A_101, B_102, D_99)) | k1_xboole_0=B_102 | ~r2_hidden(C_100, A_101) | ~m1_subset_1(D_99, k1_zfmisc_1(k2_zfmisc_1(A_101, B_102))) | ~v1_funct_2(D_99, A_101, B_102) | ~v1_funct_1(D_99))), inference(cnfTransformation, [status(thm)], [f_78])).
% 5.84/2.11  tff(c_341, plain, (![C_100]: (r2_hidden(k1_funct_1('#skF_6', C_100), k2_relat_1('#skF_6')) | k1_xboole_0='#skF_5' | ~r2_hidden(C_100, '#skF_4') | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5'))) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5') | ~v1_funct_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_269, c_333])).
% 5.84/2.11  tff(c_348, plain, (![C_100]: (r2_hidden(k1_funct_1('#skF_6', C_100), k2_relat_1('#skF_6')) | k1_xboole_0='#skF_5' | ~r2_hidden(C_100, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_36, c_341])).
% 5.84/2.11  tff(c_421, plain, (k1_xboole_0='#skF_5'), inference(splitLeft, [status(thm)], [c_348])).
% 5.84/2.11  tff(c_16, plain, (![A_9]: (r1_tarski(k1_xboole_0, A_9))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.84/2.11  tff(c_22, plain, (![B_13, A_12]: (~r1_tarski(B_13, A_12) | ~r2_hidden(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_52])).
% 5.84/2.11  tff(c_169, plain, (![B_74, A_75, B_76]: (~r1_tarski(B_74, '#skF_1'(A_75, B_76)) | ~r1_tarski(A_75, B_74) | r1_tarski(A_75, B_76))), inference(resolution, [status(thm)], [c_146, c_22])).
% 5.84/2.11  tff(c_185, plain, (![A_77, B_78]: (~r1_tarski(A_77, k1_xboole_0) | r1_tarski(A_77, B_78))), inference(resolution, [status(thm)], [c_16, c_169])).
% 5.84/2.11  tff(c_195, plain, (![B_11, B_78]: (r1_tarski(k2_relat_1(B_11), B_78) | ~v5_relat_1(B_11, k1_xboole_0) | ~v1_relat_1(B_11))), inference(resolution, [status(thm)], [c_20, c_185])).
% 5.84/2.11  tff(c_243, plain, (![A_87, B_88]: (r2_hidden('#skF_2'(A_87, B_88), B_88) | r2_hidden('#skF_3'(A_87, B_88), A_87) | B_88=A_87)), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.84/2.11  tff(c_275, plain, (![B_92, A_93]: (~r1_tarski(B_92, '#skF_2'(A_93, B_92)) | r2_hidden('#skF_3'(A_93, B_92), A_93) | B_92=A_93)), inference(resolution, [status(thm)], [c_243, c_22])).
% 5.84/2.11  tff(c_288, plain, (![A_94]: (r2_hidden('#skF_3'(A_94, k1_xboole_0), A_94) | k1_xboole_0=A_94)), inference(resolution, [status(thm)], [c_16, c_275])).
% 5.84/2.11  tff(c_302, plain, (![A_95]: (~r1_tarski(A_95, '#skF_3'(A_95, k1_xboole_0)) | k1_xboole_0=A_95)), inference(resolution, [status(thm)], [c_288, c_22])).
% 5.84/2.11  tff(c_315, plain, (![B_11]: (k2_relat_1(B_11)=k1_xboole_0 | ~v5_relat_1(B_11, k1_xboole_0) | ~v1_relat_1(B_11))), inference(resolution, [status(thm)], [c_195, c_302])).
% 5.84/2.11  tff(c_575, plain, (![B_124]: (k2_relat_1(B_124)='#skF_5' | ~v5_relat_1(B_124, '#skF_5') | ~v1_relat_1(B_124))), inference(demodulation, [status(thm), theory('equality')], [c_421, c_421, c_315])).
% 5.84/2.11  tff(c_578, plain, (k2_relat_1('#skF_6')='#skF_5' | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_122, c_575])).
% 5.84/2.11  tff(c_581, plain, (k2_relat_1('#skF_6')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_57, c_578])).
% 5.84/2.11  tff(c_583, plain, $false, inference(negUnitSimplification, [status(thm)], [c_270, c_581])).
% 5.84/2.11  tff(c_585, plain, (k1_xboole_0!='#skF_5'), inference(splitRight, [status(thm)], [c_348])).
% 5.84/2.11  tff(c_44, plain, (![D_30]: (r2_hidden('#skF_7'(D_30), '#skF_4') | ~r2_hidden(D_30, '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_97])).
% 5.84/2.11  tff(c_42, plain, (![D_30]: (k1_funct_1('#skF_6', '#skF_7'(D_30))=D_30 | ~r2_hidden(D_30, '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_97])).
% 5.84/2.11  tff(c_344, plain, (![D_30, A_101, B_102]: (r2_hidden(D_30, k2_relset_1(A_101, B_102, '#skF_6')) | k1_xboole_0=B_102 | ~r2_hidden('#skF_7'(D_30), A_101) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(A_101, B_102))) | ~v1_funct_2('#skF_6', A_101, B_102) | ~v1_funct_1('#skF_6') | ~r2_hidden(D_30, '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_42, c_333])).
% 5.84/2.11  tff(c_414, plain, (![D_107, A_108, B_109]: (r2_hidden(D_107, k2_relset_1(A_108, B_109, '#skF_6')) | k1_xboole_0=B_109 | ~r2_hidden('#skF_7'(D_107), A_108) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(A_108, B_109))) | ~v1_funct_2('#skF_6', A_108, B_109) | ~r2_hidden(D_107, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_344])).
% 5.84/2.11  tff(c_586, plain, (![D_125, B_126]: (r2_hidden(D_125, k2_relset_1('#skF_4', B_126, '#skF_6')) | k1_xboole_0=B_126 | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', B_126))) | ~v1_funct_2('#skF_6', '#skF_4', B_126) | ~r2_hidden(D_125, '#skF_5'))), inference(resolution, [status(thm)], [c_44, c_414])).
% 5.84/2.11  tff(c_588, plain, (![D_125]: (r2_hidden(D_125, k2_relset_1('#skF_4', '#skF_5', '#skF_6')) | k1_xboole_0='#skF_5' | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5') | ~r2_hidden(D_125, '#skF_5'))), inference(resolution, [status(thm)], [c_36, c_586])).
% 5.84/2.11  tff(c_591, plain, (![D_125]: (r2_hidden(D_125, k2_relat_1('#skF_6')) | k1_xboole_0='#skF_5' | ~r2_hidden(D_125, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_269, c_588])).
% 5.84/2.11  tff(c_604, plain, (![D_128]: (r2_hidden(D_128, k2_relat_1('#skF_6')) | ~r2_hidden(D_128, '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_585, c_591])).
% 5.84/2.11  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.84/2.11  tff(c_628, plain, (![A_1]: (r1_tarski(A_1, k2_relat_1('#skF_6')) | ~r2_hidden('#skF_1'(A_1, k2_relat_1('#skF_6')), '#skF_5'))), inference(resolution, [status(thm)], [c_604, c_4])).
% 5.84/2.11  tff(c_3601, plain, (![B_439]: (r1_tarski(k2_relat_1(B_439), k2_relat_1('#skF_6')) | ~v5_relat_1(B_439, '#skF_5') | ~v1_relat_1(B_439))), inference(resolution, [status(thm)], [c_3579, c_628])).
% 5.84/2.11  tff(c_18, plain, (![B_11, A_10]: (v5_relat_1(B_11, A_10) | ~r1_tarski(k2_relat_1(B_11), A_10) | ~v1_relat_1(B_11))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.84/2.11  tff(c_3739, plain, (![B_439]: (v5_relat_1(B_439, k2_relat_1('#skF_6')) | ~v5_relat_1(B_439, '#skF_5') | ~v1_relat_1(B_439))), inference(resolution, [status(thm)], [c_3601, c_18])).
% 5.84/2.11  tff(c_761, plain, (![A_141]: (r1_tarski(A_141, k2_relat_1('#skF_6')) | ~r2_hidden('#skF_1'(A_141, k2_relat_1('#skF_6')), '#skF_5'))), inference(resolution, [status(thm)], [c_604, c_4])).
% 5.84/2.11  tff(c_771, plain, (r1_tarski('#skF_5', k2_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_6, c_761])).
% 5.84/2.11  tff(c_1153, plain, (![A_173, B_174, B_175]: (r2_hidden('#skF_3'(A_173, B_174), B_175) | ~r1_tarski(A_173, B_175) | r2_hidden('#skF_2'(A_173, B_174), B_174) | B_174=A_173)), inference(resolution, [status(thm)], [c_243, c_2])).
% 5.84/2.11  tff(c_10, plain, (![A_6, B_7]: (r2_hidden('#skF_2'(A_6, B_7), B_7) | ~r2_hidden('#skF_3'(A_6, B_7), B_7) | B_7=A_6)), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.84/2.11  tff(c_1270, plain, (![A_179, B_180]: (~r1_tarski(A_179, B_180) | r2_hidden('#skF_2'(A_179, B_180), B_180) | B_180=A_179)), inference(resolution, [status(thm)], [c_1153, c_10])).
% 5.84/2.11  tff(c_1302, plain, (![A_179, B_180, B_2]: (r2_hidden('#skF_2'(A_179, B_180), B_2) | ~r1_tarski(B_180, B_2) | ~r1_tarski(A_179, B_180) | B_180=A_179)), inference(resolution, [status(thm)], [c_1270, c_2])).
% 5.84/2.11  tff(c_12, plain, (![A_6, B_7]: (~r2_hidden('#skF_2'(A_6, B_7), A_6) | r2_hidden('#skF_3'(A_6, B_7), A_6) | B_7=A_6)), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.84/2.11  tff(c_603, plain, (![D_125]: (r2_hidden(D_125, k2_relat_1('#skF_6')) | ~r2_hidden(D_125, '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_585, c_591])).
% 5.84/2.11  tff(c_14, plain, (![A_6, B_7]: (r2_hidden('#skF_2'(A_6, B_7), B_7) | r2_hidden('#skF_3'(A_6, B_7), A_6) | B_7=A_6)), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.84/2.11  tff(c_817, plain, (![D_148, B_149]: (r2_hidden(D_148, B_149) | ~r1_tarski(k2_relat_1('#skF_6'), B_149) | ~r2_hidden(D_148, '#skF_5'))), inference(resolution, [status(thm)], [c_604, c_2])).
% 5.84/2.11  tff(c_826, plain, (![D_148, A_10]: (r2_hidden(D_148, A_10) | ~r2_hidden(D_148, '#skF_5') | ~v5_relat_1('#skF_6', A_10) | ~v1_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_20, c_817])).
% 5.84/2.11  tff(c_838, plain, (![D_150, A_151]: (r2_hidden(D_150, A_151) | ~r2_hidden(D_150, '#skF_5') | ~v5_relat_1('#skF_6', A_151))), inference(demodulation, [status(thm), theory('equality')], [c_57, c_826])).
% 5.84/2.11  tff(c_3850, plain, (![B_448, A_449]: (r2_hidden('#skF_3'('#skF_5', B_448), A_449) | ~v5_relat_1('#skF_6', A_449) | r2_hidden('#skF_2'('#skF_5', B_448), B_448) | B_448='#skF_5')), inference(resolution, [status(thm)], [c_14, c_838])).
% 5.84/2.11  tff(c_3901, plain, (![A_450]: (~v5_relat_1('#skF_6', A_450) | r2_hidden('#skF_2'('#skF_5', A_450), A_450) | A_450='#skF_5')), inference(resolution, [status(thm)], [c_3850, c_10])).
% 5.84/2.11  tff(c_3972, plain, (![A_456, B_457]: (r2_hidden('#skF_2'('#skF_5', A_456), B_457) | ~r1_tarski(A_456, B_457) | ~v5_relat_1('#skF_6', A_456) | A_456='#skF_5')), inference(resolution, [status(thm)], [c_3901, c_2])).
% 5.84/2.11  tff(c_8, plain, (![A_6, B_7]: (~r2_hidden('#skF_2'(A_6, B_7), A_6) | ~r2_hidden('#skF_3'(A_6, B_7), B_7) | B_7=A_6)), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.84/2.11  tff(c_4007, plain, (![A_460]: (~r2_hidden('#skF_3'('#skF_5', A_460), A_460) | ~r1_tarski(A_460, '#skF_5') | ~v5_relat_1('#skF_6', A_460) | A_460='#skF_5')), inference(resolution, [status(thm)], [c_3972, c_8])).
% 5.84/2.11  tff(c_4055, plain, (~r1_tarski(k2_relat_1('#skF_6'), '#skF_5') | ~v5_relat_1('#skF_6', k2_relat_1('#skF_6')) | k2_relat_1('#skF_6')='#skF_5' | ~r2_hidden('#skF_3'('#skF_5', k2_relat_1('#skF_6')), '#skF_5')), inference(resolution, [status(thm)], [c_603, c_4007])).
% 5.84/2.11  tff(c_4098, plain, (~r1_tarski(k2_relat_1('#skF_6'), '#skF_5') | ~v5_relat_1('#skF_6', k2_relat_1('#skF_6')) | ~r2_hidden('#skF_3'('#skF_5', k2_relat_1('#skF_6')), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_270, c_4055])).
% 5.84/2.11  tff(c_4287, plain, (~r2_hidden('#skF_3'('#skF_5', k2_relat_1('#skF_6')), '#skF_5')), inference(splitLeft, [status(thm)], [c_4098])).
% 5.84/2.11  tff(c_4311, plain, (~r2_hidden('#skF_2'('#skF_5', k2_relat_1('#skF_6')), '#skF_5') | k2_relat_1('#skF_6')='#skF_5'), inference(resolution, [status(thm)], [c_12, c_4287])).
% 5.84/2.11  tff(c_4335, plain, (~r2_hidden('#skF_2'('#skF_5', k2_relat_1('#skF_6')), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_270, c_4311])).
% 5.84/2.11  tff(c_4345, plain, (~r1_tarski(k2_relat_1('#skF_6'), '#skF_5') | ~r1_tarski('#skF_5', k2_relat_1('#skF_6')) | k2_relat_1('#skF_6')='#skF_5'), inference(resolution, [status(thm)], [c_1302, c_4335])).
% 5.84/2.11  tff(c_4354, plain, (~r1_tarski(k2_relat_1('#skF_6'), '#skF_5') | k2_relat_1('#skF_6')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_771, c_4345])).
% 5.84/2.11  tff(c_4355, plain, (~r1_tarski(k2_relat_1('#skF_6'), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_270, c_4354])).
% 5.84/2.11  tff(c_4361, plain, (~v5_relat_1('#skF_6', '#skF_5') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_20, c_4355])).
% 5.84/2.11  tff(c_4368, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_57, c_122, c_4361])).
% 5.84/2.11  tff(c_4369, plain, (~v5_relat_1('#skF_6', k2_relat_1('#skF_6')) | ~r1_tarski(k2_relat_1('#skF_6'), '#skF_5')), inference(splitRight, [status(thm)], [c_4098])).
% 5.84/2.11  tff(c_4381, plain, (~r1_tarski(k2_relat_1('#skF_6'), '#skF_5')), inference(splitLeft, [status(thm)], [c_4369])).
% 5.84/2.11  tff(c_4387, plain, (~v5_relat_1('#skF_6', '#skF_5') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_20, c_4381])).
% 5.84/2.11  tff(c_4394, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_57, c_122, c_4387])).
% 5.84/2.11  tff(c_4395, plain, (~v5_relat_1('#skF_6', k2_relat_1('#skF_6'))), inference(splitRight, [status(thm)], [c_4369])).
% 5.84/2.11  tff(c_4399, plain, (~v5_relat_1('#skF_6', '#skF_5') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_3739, c_4395])).
% 5.84/2.11  tff(c_4409, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_57, c_122, c_4399])).
% 5.84/2.11  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.84/2.11  
% 5.84/2.11  Inference rules
% 5.84/2.11  ----------------------
% 5.84/2.11  #Ref     : 0
% 5.84/2.11  #Sup     : 854
% 5.84/2.11  #Fact    : 0
% 5.84/2.11  #Define  : 0
% 5.84/2.11  #Split   : 11
% 5.84/2.11  #Chain   : 0
% 5.84/2.11  #Close   : 0
% 5.84/2.11  
% 5.84/2.11  Ordering : KBO
% 5.84/2.11  
% 5.84/2.11  Simplification rules
% 5.84/2.11  ----------------------
% 5.84/2.11  #Subsume      : 403
% 5.84/2.11  #Demod        : 327
% 5.84/2.11  #Tautology    : 97
% 5.84/2.11  #SimpNegUnit  : 54
% 5.84/2.11  #BackRed      : 14
% 5.84/2.11  
% 5.84/2.11  #Partial instantiations: 0
% 5.84/2.11  #Strategies tried      : 1
% 5.84/2.11  
% 5.84/2.11  Timing (in seconds)
% 5.84/2.11  ----------------------
% 5.84/2.12  Preprocessing        : 0.31
% 5.84/2.12  Parsing              : 0.16
% 5.84/2.12  CNF conversion       : 0.02
% 5.84/2.12  Main loop            : 1.03
% 5.84/2.12  Inferencing          : 0.37
% 5.84/2.12  Reduction            : 0.27
% 5.84/2.12  Demodulation         : 0.17
% 5.84/2.12  BG Simplification    : 0.03
% 5.84/2.12  Subsumption          : 0.29
% 5.84/2.12  Abstraction          : 0.04
% 5.84/2.12  MUC search           : 0.00
% 5.84/2.12  Cooper               : 0.00
% 5.84/2.12  Total                : 1.38
% 5.84/2.12  Index Insertion      : 0.00
% 5.84/2.12  Index Deletion       : 0.00
% 5.84/2.12  Index Matching       : 0.00
% 5.84/2.12  BG Taut test         : 0.00
%------------------------------------------------------------------------------
