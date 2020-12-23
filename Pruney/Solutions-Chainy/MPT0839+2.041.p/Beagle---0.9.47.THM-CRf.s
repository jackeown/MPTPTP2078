%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:27 EST 2020

% Result     : Theorem 2.88s
% Output     : CNFRefutation 3.16s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 324 expanded)
%              Number of leaves         :   37 ( 123 expanded)
%              Depth                    :   12
%              Number of atoms          :  154 ( 658 expanded)
%              Number of equality atoms :   37 ( 113 expanded)
%              Maximal formula depth    :   13 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_116,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ~ v1_xboole_0(B)
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
               => ~ ( k2_relset_1(B,A,C) != k1_xboole_0
                    & ! [D] :
                        ( m1_subset_1(D,B)
                       => ~ r2_hidden(D,k1_relset_1(B,A,C)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_relset_1)).

tff(f_95,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_77,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_57,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_32,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_75,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_xboole_0(B) )
     => ( v1_xboole_0(k7_relat_1(A,B))
        & v1_relat_1(k7_relat_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc16_relat_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).

tff(f_87,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_91,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_44,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_81,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k7_relat_1(A,k1_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_relat_1)).

tff(f_67,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_xboole_0(k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc11_relat_1)).

tff(c_44,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_975,plain,(
    ! [A_171,B_172,C_173] :
      ( k2_relset_1(A_171,B_172,C_173) = k2_relat_1(C_173)
      | ~ m1_subset_1(C_173,k1_zfmisc_1(k2_zfmisc_1(A_171,B_172))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_989,plain,(
    k2_relset_1('#skF_3','#skF_2','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_975])).

tff(c_42,plain,(
    k2_relset_1('#skF_3','#skF_2','#skF_4') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_990,plain,(
    k2_relat_1('#skF_4') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_989,c_42])).

tff(c_28,plain,(
    ! [A_20,B_21] : v1_relat_1(k2_zfmisc_1(A_20,B_21)) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_745,plain,(
    ! [B_130,A_131] :
      ( v1_relat_1(B_130)
      | ~ m1_subset_1(B_130,k1_zfmisc_1(A_131))
      | ~ v1_relat_1(A_131) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_751,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_2')) ),
    inference(resolution,[status(thm)],[c_44,c_745])).

tff(c_755,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_751])).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_151,plain,(
    ! [B_63,A_64] :
      ( v1_relat_1(B_63)
      | ~ m1_subset_1(B_63,k1_zfmisc_1(A_64))
      | ~ v1_relat_1(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_157,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_2')) ),
    inference(resolution,[status(thm)],[c_44,c_151])).

tff(c_161,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_157])).

tff(c_169,plain,(
    ! [A_67,B_68] :
      ( v1_xboole_0(k7_relat_1(A_67,B_68))
      | ~ v1_xboole_0(B_68)
      | ~ v1_relat_1(A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_63,plain,(
    ! [B_51,A_52] :
      ( ~ v1_xboole_0(B_51)
      | B_51 = A_52
      | ~ v1_xboole_0(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_69,plain,(
    ! [A_52] :
      ( k1_xboole_0 = A_52
      | ~ v1_xboole_0(A_52) ) ),
    inference(resolution,[status(thm)],[c_6,c_63])).

tff(c_202,plain,(
    ! [A_73,B_74] :
      ( k7_relat_1(A_73,B_74) = k1_xboole_0
      | ~ v1_xboole_0(B_74)
      | ~ v1_relat_1(A_73) ) ),
    inference(resolution,[status(thm)],[c_169,c_69])).

tff(c_213,plain,(
    ! [A_77] :
      ( k7_relat_1(A_77,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_77) ) ),
    inference(resolution,[status(thm)],[c_6,c_202])).

tff(c_224,plain,(
    k7_relat_1('#skF_4',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_161,c_213])).

tff(c_305,plain,(
    ! [C_88,A_89,B_90] :
      ( v4_relat_1(C_88,A_89)
      | ~ m1_subset_1(C_88,k1_zfmisc_1(k2_zfmisc_1(A_89,B_90))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_314,plain,(
    v4_relat_1('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_305])).

tff(c_20,plain,(
    ! [B_16,A_15] :
      ( r1_tarski(k1_relat_1(B_16),A_15)
      | ~ v4_relat_1(B_16,A_15)
      | ~ v1_relat_1(B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_464,plain,(
    ! [A_115,B_116,C_117] :
      ( k1_relset_1(A_115,B_116,C_117) = k1_relat_1(C_117)
      | ~ m1_subset_1(C_117,k1_zfmisc_1(k2_zfmisc_1(A_115,B_116))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_478,plain,(
    k1_relset_1('#skF_3','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_464])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_12,plain,(
    ! [A_7,B_8] :
      ( m1_subset_1(A_7,k1_zfmisc_1(B_8))
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_373,plain,(
    ! [A_99,C_100,B_101] :
      ( m1_subset_1(A_99,C_100)
      | ~ m1_subset_1(B_101,k1_zfmisc_1(C_100))
      | ~ r2_hidden(A_99,B_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_381,plain,(
    ! [A_103,B_104,A_105] :
      ( m1_subset_1(A_103,B_104)
      | ~ r2_hidden(A_103,A_105)
      | ~ r1_tarski(A_105,B_104) ) ),
    inference(resolution,[status(thm)],[c_12,c_373])).

tff(c_385,plain,(
    ! [A_106,B_107] :
      ( m1_subset_1('#skF_1'(A_106),B_107)
      | ~ r1_tarski(A_106,B_107)
      | v1_xboole_0(A_106) ) ),
    inference(resolution,[status(thm)],[c_4,c_381])).

tff(c_57,plain,(
    ! [D_50] :
      ( ~ r2_hidden(D_50,k1_relset_1('#skF_3','#skF_2','#skF_4'))
      | ~ m1_subset_1(D_50,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_62,plain,
    ( ~ m1_subset_1('#skF_1'(k1_relset_1('#skF_3','#skF_2','#skF_4')),'#skF_3')
    | v1_xboole_0(k1_relset_1('#skF_3','#skF_2','#skF_4')) ),
    inference(resolution,[status(thm)],[c_4,c_57])).

tff(c_143,plain,(
    ~ m1_subset_1('#skF_1'(k1_relset_1('#skF_3','#skF_2','#skF_4')),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_62])).

tff(c_412,plain,
    ( ~ r1_tarski(k1_relset_1('#skF_3','#skF_2','#skF_4'),'#skF_3')
    | v1_xboole_0(k1_relset_1('#skF_3','#skF_2','#skF_4')) ),
    inference(resolution,[status(thm)],[c_385,c_143])).

tff(c_414,plain,(
    ~ r1_tarski(k1_relset_1('#skF_3','#skF_2','#skF_4'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_412])).

tff(c_479,plain,(
    ~ r1_tarski(k1_relat_1('#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_478,c_414])).

tff(c_488,plain,
    ( ~ v4_relat_1('#skF_4','#skF_3')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_20,c_479])).

tff(c_492,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_161,c_314,c_488])).

tff(c_493,plain,(
    v1_xboole_0(k1_relset_1('#skF_3','#skF_2','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_412])).

tff(c_516,plain,(
    k1_relset_1('#skF_3','#skF_2','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_493,c_69])).

tff(c_545,plain,(
    ! [A_119,B_120,C_121] :
      ( k1_relset_1(A_119,B_120,C_121) = k1_relat_1(C_121)
      | ~ m1_subset_1(C_121,k1_zfmisc_1(k2_zfmisc_1(A_119,B_120))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_556,plain,(
    k1_relset_1('#skF_3','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_545])).

tff(c_560,plain,(
    k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_516,c_556])).

tff(c_30,plain,(
    ! [A_22] :
      ( k7_relat_1(A_22,k1_relat_1(A_22)) = A_22
      | ~ v1_relat_1(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_573,plain,
    ( k7_relat_1('#skF_4',k1_xboole_0) = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_560,c_30])).

tff(c_583,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_161,c_224,c_573])).

tff(c_624,plain,(
    k2_relset_1('#skF_3','#skF_2','#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_583,c_42])).

tff(c_22,plain,(
    ! [A_17] :
      ( v1_xboole_0(k2_relat_1(A_17))
      | ~ v1_xboole_0(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_70,plain,(
    ! [A_53] :
      ( k1_xboole_0 = A_53
      | ~ v1_xboole_0(A_53) ) ),
    inference(resolution,[status(thm)],[c_6,c_63])).

tff(c_80,plain,(
    ! [A_54] :
      ( k2_relat_1(A_54) = k1_xboole_0
      | ~ v1_xboole_0(A_54) ) ),
    inference(resolution,[status(thm)],[c_22,c_70])).

tff(c_88,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_80])).

tff(c_621,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_583,c_583,c_88])).

tff(c_672,plain,(
    ! [A_122,B_123,C_124] :
      ( k2_relset_1(A_122,B_123,C_124) = k2_relat_1(C_124)
      | ~ m1_subset_1(C_124,k1_zfmisc_1(k2_zfmisc_1(A_122,B_123))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_683,plain,(
    k2_relset_1('#skF_3','#skF_2','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_672])).

tff(c_687,plain,(
    k2_relset_1('#skF_3','#skF_2','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_621,c_683])).

tff(c_689,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_624,c_687])).

tff(c_690,plain,(
    v1_xboole_0(k1_relset_1('#skF_3','#skF_2','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_701,plain,(
    k1_relset_1('#skF_3','#skF_2','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_690,c_69])).

tff(c_1048,plain,(
    ! [A_181,B_182,C_183] :
      ( k1_relset_1(A_181,B_182,C_183) = k1_relat_1(C_183)
      | ~ m1_subset_1(C_183,k1_zfmisc_1(k2_zfmisc_1(A_181,B_182))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_1059,plain,(
    k1_relset_1('#skF_3','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_1048])).

tff(c_1063,plain,(
    k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_701,c_1059])).

tff(c_727,plain,(
    ! [A_128,B_129] :
      ( v1_xboole_0(k7_relat_1(A_128,B_129))
      | ~ v1_xboole_0(B_129)
      | ~ v1_relat_1(A_128) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_740,plain,(
    ! [A_22] :
      ( v1_xboole_0(A_22)
      | ~ v1_xboole_0(k1_relat_1(A_22))
      | ~ v1_relat_1(A_22)
      | ~ v1_relat_1(A_22) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_727])).

tff(c_1067,plain,
    ( v1_xboole_0('#skF_4')
    | ~ v1_xboole_0(k1_xboole_0)
    | ~ v1_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1063,c_740])).

tff(c_1080,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_755,c_755,c_6,c_1067])).

tff(c_77,plain,(
    ! [A_17] :
      ( k2_relat_1(A_17) = k1_xboole_0
      | ~ v1_xboole_0(A_17) ) ),
    inference(resolution,[status(thm)],[c_22,c_70])).

tff(c_1100,plain,(
    k2_relat_1('#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1080,c_77])).

tff(c_1114,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_990,c_1100])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.33  % Computer   : n003.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % DateTime   : Tue Dec  1 11:46:57 EST 2020
% 0.14/0.33  % CPUTime    : 
% 0.14/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.88/1.43  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.16/1.44  
% 3.16/1.44  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.16/1.44  %$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 3.16/1.44  
% 3.16/1.44  %Foreground sorts:
% 3.16/1.44  
% 3.16/1.44  
% 3.16/1.44  %Background operators:
% 3.16/1.44  
% 3.16/1.44  
% 3.16/1.44  %Foreground operators:
% 3.16/1.44  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.16/1.44  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.16/1.44  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.16/1.44  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.16/1.44  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.16/1.44  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.16/1.44  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.16/1.44  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.16/1.44  tff('#skF_2', type, '#skF_2': $i).
% 3.16/1.44  tff('#skF_3', type, '#skF_3': $i).
% 3.16/1.44  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.16/1.44  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.16/1.44  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.16/1.44  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.16/1.44  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.16/1.44  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.16/1.44  tff('#skF_4', type, '#skF_4': $i).
% 3.16/1.44  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.16/1.44  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.16/1.44  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.16/1.44  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.16/1.44  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.16/1.44  
% 3.16/1.46  tff(f_116, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => ~(~(k2_relset_1(B, A, C) = k1_xboole_0) & (![D]: (m1_subset_1(D, B) => ~r2_hidden(D, k1_relset_1(B, A, C))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_relset_1)).
% 3.16/1.46  tff(f_95, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.16/1.46  tff(f_77, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.16/1.46  tff(f_57, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.16/1.46  tff(f_32, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.16/1.46  tff(f_75, axiom, (![A, B]: ((v1_relat_1(A) & v1_xboole_0(B)) => (v1_xboole_0(k7_relat_1(A, B)) & v1_relat_1(k7_relat_1(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc16_relat_1)).
% 3.16/1.46  tff(f_40, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_boole)).
% 3.16/1.46  tff(f_87, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.16/1.46  tff(f_63, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 3.16/1.46  tff(f_91, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.16/1.46  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 3.16/1.46  tff(f_44, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 3.16/1.46  tff(f_50, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 3.16/1.46  tff(f_81, axiom, (![A]: (v1_relat_1(A) => (k7_relat_1(A, k1_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_relat_1)).
% 3.16/1.46  tff(f_67, axiom, (![A]: (v1_xboole_0(A) => v1_xboole_0(k2_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc11_relat_1)).
% 3.16/1.46  tff(c_44, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_116])).
% 3.16/1.46  tff(c_975, plain, (![A_171, B_172, C_173]: (k2_relset_1(A_171, B_172, C_173)=k2_relat_1(C_173) | ~m1_subset_1(C_173, k1_zfmisc_1(k2_zfmisc_1(A_171, B_172))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.16/1.46  tff(c_989, plain, (k2_relset_1('#skF_3', '#skF_2', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_44, c_975])).
% 3.16/1.46  tff(c_42, plain, (k2_relset_1('#skF_3', '#skF_2', '#skF_4')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_116])).
% 3.16/1.46  tff(c_990, plain, (k2_relat_1('#skF_4')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_989, c_42])).
% 3.16/1.46  tff(c_28, plain, (![A_20, B_21]: (v1_relat_1(k2_zfmisc_1(A_20, B_21)))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.16/1.46  tff(c_745, plain, (![B_130, A_131]: (v1_relat_1(B_130) | ~m1_subset_1(B_130, k1_zfmisc_1(A_131)) | ~v1_relat_1(A_131))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.16/1.46  tff(c_751, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_2'))), inference(resolution, [status(thm)], [c_44, c_745])).
% 3.16/1.46  tff(c_755, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_751])).
% 3.16/1.46  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.16/1.46  tff(c_151, plain, (![B_63, A_64]: (v1_relat_1(B_63) | ~m1_subset_1(B_63, k1_zfmisc_1(A_64)) | ~v1_relat_1(A_64))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.16/1.46  tff(c_157, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_2'))), inference(resolution, [status(thm)], [c_44, c_151])).
% 3.16/1.46  tff(c_161, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_157])).
% 3.16/1.46  tff(c_169, plain, (![A_67, B_68]: (v1_xboole_0(k7_relat_1(A_67, B_68)) | ~v1_xboole_0(B_68) | ~v1_relat_1(A_67))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.16/1.46  tff(c_63, plain, (![B_51, A_52]: (~v1_xboole_0(B_51) | B_51=A_52 | ~v1_xboole_0(A_52))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.16/1.46  tff(c_69, plain, (![A_52]: (k1_xboole_0=A_52 | ~v1_xboole_0(A_52))), inference(resolution, [status(thm)], [c_6, c_63])).
% 3.16/1.46  tff(c_202, plain, (![A_73, B_74]: (k7_relat_1(A_73, B_74)=k1_xboole_0 | ~v1_xboole_0(B_74) | ~v1_relat_1(A_73))), inference(resolution, [status(thm)], [c_169, c_69])).
% 3.16/1.46  tff(c_213, plain, (![A_77]: (k7_relat_1(A_77, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_77))), inference(resolution, [status(thm)], [c_6, c_202])).
% 3.16/1.46  tff(c_224, plain, (k7_relat_1('#skF_4', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_161, c_213])).
% 3.16/1.46  tff(c_305, plain, (![C_88, A_89, B_90]: (v4_relat_1(C_88, A_89) | ~m1_subset_1(C_88, k1_zfmisc_1(k2_zfmisc_1(A_89, B_90))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.16/1.46  tff(c_314, plain, (v4_relat_1('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_44, c_305])).
% 3.16/1.46  tff(c_20, plain, (![B_16, A_15]: (r1_tarski(k1_relat_1(B_16), A_15) | ~v4_relat_1(B_16, A_15) | ~v1_relat_1(B_16))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.16/1.46  tff(c_464, plain, (![A_115, B_116, C_117]: (k1_relset_1(A_115, B_116, C_117)=k1_relat_1(C_117) | ~m1_subset_1(C_117, k1_zfmisc_1(k2_zfmisc_1(A_115, B_116))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.16/1.46  tff(c_478, plain, (k1_relset_1('#skF_3', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_44, c_464])).
% 3.16/1.46  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.16/1.46  tff(c_12, plain, (![A_7, B_8]: (m1_subset_1(A_7, k1_zfmisc_1(B_8)) | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.16/1.46  tff(c_373, plain, (![A_99, C_100, B_101]: (m1_subset_1(A_99, C_100) | ~m1_subset_1(B_101, k1_zfmisc_1(C_100)) | ~r2_hidden(A_99, B_101))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.16/1.46  tff(c_381, plain, (![A_103, B_104, A_105]: (m1_subset_1(A_103, B_104) | ~r2_hidden(A_103, A_105) | ~r1_tarski(A_105, B_104))), inference(resolution, [status(thm)], [c_12, c_373])).
% 3.16/1.46  tff(c_385, plain, (![A_106, B_107]: (m1_subset_1('#skF_1'(A_106), B_107) | ~r1_tarski(A_106, B_107) | v1_xboole_0(A_106))), inference(resolution, [status(thm)], [c_4, c_381])).
% 3.16/1.46  tff(c_57, plain, (![D_50]: (~r2_hidden(D_50, k1_relset_1('#skF_3', '#skF_2', '#skF_4')) | ~m1_subset_1(D_50, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_116])).
% 3.16/1.46  tff(c_62, plain, (~m1_subset_1('#skF_1'(k1_relset_1('#skF_3', '#skF_2', '#skF_4')), '#skF_3') | v1_xboole_0(k1_relset_1('#skF_3', '#skF_2', '#skF_4'))), inference(resolution, [status(thm)], [c_4, c_57])).
% 3.16/1.46  tff(c_143, plain, (~m1_subset_1('#skF_1'(k1_relset_1('#skF_3', '#skF_2', '#skF_4')), '#skF_3')), inference(splitLeft, [status(thm)], [c_62])).
% 3.16/1.46  tff(c_412, plain, (~r1_tarski(k1_relset_1('#skF_3', '#skF_2', '#skF_4'), '#skF_3') | v1_xboole_0(k1_relset_1('#skF_3', '#skF_2', '#skF_4'))), inference(resolution, [status(thm)], [c_385, c_143])).
% 3.16/1.46  tff(c_414, plain, (~r1_tarski(k1_relset_1('#skF_3', '#skF_2', '#skF_4'), '#skF_3')), inference(splitLeft, [status(thm)], [c_412])).
% 3.16/1.46  tff(c_479, plain, (~r1_tarski(k1_relat_1('#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_478, c_414])).
% 3.16/1.46  tff(c_488, plain, (~v4_relat_1('#skF_4', '#skF_3') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_20, c_479])).
% 3.16/1.46  tff(c_492, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_161, c_314, c_488])).
% 3.16/1.46  tff(c_493, plain, (v1_xboole_0(k1_relset_1('#skF_3', '#skF_2', '#skF_4'))), inference(splitRight, [status(thm)], [c_412])).
% 3.16/1.46  tff(c_516, plain, (k1_relset_1('#skF_3', '#skF_2', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_493, c_69])).
% 3.16/1.46  tff(c_545, plain, (![A_119, B_120, C_121]: (k1_relset_1(A_119, B_120, C_121)=k1_relat_1(C_121) | ~m1_subset_1(C_121, k1_zfmisc_1(k2_zfmisc_1(A_119, B_120))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.16/1.46  tff(c_556, plain, (k1_relset_1('#skF_3', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_44, c_545])).
% 3.16/1.46  tff(c_560, plain, (k1_relat_1('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_516, c_556])).
% 3.16/1.46  tff(c_30, plain, (![A_22]: (k7_relat_1(A_22, k1_relat_1(A_22))=A_22 | ~v1_relat_1(A_22))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.16/1.46  tff(c_573, plain, (k7_relat_1('#skF_4', k1_xboole_0)='#skF_4' | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_560, c_30])).
% 3.16/1.46  tff(c_583, plain, (k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_161, c_224, c_573])).
% 3.16/1.46  tff(c_624, plain, (k2_relset_1('#skF_3', '#skF_2', '#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_583, c_42])).
% 3.16/1.46  tff(c_22, plain, (![A_17]: (v1_xboole_0(k2_relat_1(A_17)) | ~v1_xboole_0(A_17))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.16/1.46  tff(c_70, plain, (![A_53]: (k1_xboole_0=A_53 | ~v1_xboole_0(A_53))), inference(resolution, [status(thm)], [c_6, c_63])).
% 3.16/1.46  tff(c_80, plain, (![A_54]: (k2_relat_1(A_54)=k1_xboole_0 | ~v1_xboole_0(A_54))), inference(resolution, [status(thm)], [c_22, c_70])).
% 3.16/1.46  tff(c_88, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_6, c_80])).
% 3.16/1.46  tff(c_621, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_583, c_583, c_88])).
% 3.16/1.46  tff(c_672, plain, (![A_122, B_123, C_124]: (k2_relset_1(A_122, B_123, C_124)=k2_relat_1(C_124) | ~m1_subset_1(C_124, k1_zfmisc_1(k2_zfmisc_1(A_122, B_123))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.16/1.46  tff(c_683, plain, (k2_relset_1('#skF_3', '#skF_2', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_44, c_672])).
% 3.16/1.46  tff(c_687, plain, (k2_relset_1('#skF_3', '#skF_2', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_621, c_683])).
% 3.16/1.46  tff(c_689, plain, $false, inference(negUnitSimplification, [status(thm)], [c_624, c_687])).
% 3.16/1.46  tff(c_690, plain, (v1_xboole_0(k1_relset_1('#skF_3', '#skF_2', '#skF_4'))), inference(splitRight, [status(thm)], [c_62])).
% 3.16/1.46  tff(c_701, plain, (k1_relset_1('#skF_3', '#skF_2', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_690, c_69])).
% 3.16/1.46  tff(c_1048, plain, (![A_181, B_182, C_183]: (k1_relset_1(A_181, B_182, C_183)=k1_relat_1(C_183) | ~m1_subset_1(C_183, k1_zfmisc_1(k2_zfmisc_1(A_181, B_182))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.16/1.46  tff(c_1059, plain, (k1_relset_1('#skF_3', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_44, c_1048])).
% 3.16/1.46  tff(c_1063, plain, (k1_relat_1('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_701, c_1059])).
% 3.16/1.46  tff(c_727, plain, (![A_128, B_129]: (v1_xboole_0(k7_relat_1(A_128, B_129)) | ~v1_xboole_0(B_129) | ~v1_relat_1(A_128))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.16/1.46  tff(c_740, plain, (![A_22]: (v1_xboole_0(A_22) | ~v1_xboole_0(k1_relat_1(A_22)) | ~v1_relat_1(A_22) | ~v1_relat_1(A_22))), inference(superposition, [status(thm), theory('equality')], [c_30, c_727])).
% 3.16/1.46  tff(c_1067, plain, (v1_xboole_0('#skF_4') | ~v1_xboole_0(k1_xboole_0) | ~v1_relat_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1063, c_740])).
% 3.16/1.46  tff(c_1080, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_755, c_755, c_6, c_1067])).
% 3.16/1.46  tff(c_77, plain, (![A_17]: (k2_relat_1(A_17)=k1_xboole_0 | ~v1_xboole_0(A_17))), inference(resolution, [status(thm)], [c_22, c_70])).
% 3.16/1.46  tff(c_1100, plain, (k2_relat_1('#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_1080, c_77])).
% 3.16/1.46  tff(c_1114, plain, $false, inference(negUnitSimplification, [status(thm)], [c_990, c_1100])).
% 3.16/1.46  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.16/1.46  
% 3.16/1.46  Inference rules
% 3.16/1.46  ----------------------
% 3.16/1.46  #Ref     : 0
% 3.16/1.46  #Sup     : 246
% 3.16/1.46  #Fact    : 0
% 3.16/1.46  #Define  : 0
% 3.16/1.46  #Split   : 3
% 3.16/1.46  #Chain   : 0
% 3.16/1.46  #Close   : 0
% 3.16/1.46  
% 3.16/1.46  Ordering : KBO
% 3.16/1.46  
% 3.16/1.46  Simplification rules
% 3.16/1.46  ----------------------
% 3.16/1.46  #Subsume      : 16
% 3.16/1.46  #Demod        : 166
% 3.16/1.46  #Tautology    : 102
% 3.16/1.46  #SimpNegUnit  : 2
% 3.16/1.46  #BackRed      : 27
% 3.16/1.46  
% 3.16/1.46  #Partial instantiations: 0
% 3.16/1.46  #Strategies tried      : 1
% 3.16/1.46  
% 3.16/1.46  Timing (in seconds)
% 3.16/1.46  ----------------------
% 3.16/1.46  Preprocessing        : 0.31
% 3.16/1.46  Parsing              : 0.17
% 3.16/1.46  CNF conversion       : 0.02
% 3.16/1.46  Main loop            : 0.39
% 3.16/1.46  Inferencing          : 0.14
% 3.16/1.46  Reduction            : 0.11
% 3.16/1.46  Demodulation         : 0.08
% 3.16/1.46  BG Simplification    : 0.02
% 3.16/1.46  Subsumption          : 0.07
% 3.16/1.46  Abstraction          : 0.02
% 3.16/1.46  MUC search           : 0.00
% 3.16/1.46  Cooper               : 0.00
% 3.16/1.46  Total                : 0.74
% 3.16/1.46  Index Insertion      : 0.00
% 3.16/1.46  Index Deletion       : 0.00
% 3.16/1.46  Index Matching       : 0.00
% 3.16/1.46  BG Taut test         : 0.00
%------------------------------------------------------------------------------
