%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:14 EST 2020

% Result     : Theorem 4.27s
% Output     : CNFRefutation 4.56s
% Verified   : 
% Statistics : Number of formulae       :  182 (1098 expanded)
%              Number of leaves         :   31 ( 368 expanded)
%              Depth                    :   16
%              Number of atoms          :  397 (3436 expanded)
%              Number of equality atoms :   97 ( 882 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_114,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( r1_tarski(B,C)
         => ( ( B = k1_xboole_0
              & A != k1_xboole_0 )
            | ( v1_funct_1(D)
              & v1_funct_2(D,A,C)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,C))) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_funct_2)).

tff(f_58,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_64,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => ! [C] :
          ( ( v1_relat_1(C)
            & v5_relat_1(C,A) )
         => v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t218_relat_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_76,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_68,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_94,axiom,(
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

tff(c_48,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_59,plain,(
    ! [C_29,A_30,B_31] :
      ( v1_relat_1(C_29)
      | ~ m1_subset_1(C_29,k1_zfmisc_1(k2_zfmisc_1(A_30,B_31))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_63,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_59])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_46,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_103,plain,(
    ! [C_41,B_42,A_43] :
      ( v5_relat_1(C_41,B_42)
      | ~ m1_subset_1(C_41,k1_zfmisc_1(k2_zfmisc_1(A_43,B_42))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_107,plain,(
    v5_relat_1('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_48,c_103])).

tff(c_1525,plain,(
    ! [C_190,B_191,A_192] :
      ( v5_relat_1(C_190,B_191)
      | ~ v5_relat_1(C_190,A_192)
      | ~ v1_relat_1(C_190)
      | ~ r1_tarski(A_192,B_191) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_1527,plain,(
    ! [B_191] :
      ( v5_relat_1('#skF_4',B_191)
      | ~ v1_relat_1('#skF_4')
      | ~ r1_tarski('#skF_2',B_191) ) ),
    inference(resolution,[status(thm)],[c_107,c_1525])).

tff(c_1535,plain,(
    ! [B_194] :
      ( v5_relat_1('#skF_4',B_194)
      | ~ r1_tarski('#skF_2',B_194) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_1527])).

tff(c_18,plain,(
    ! [C_11,B_9,A_8] :
      ( v5_relat_1(C_11,B_9)
      | ~ v5_relat_1(C_11,A_8)
      | ~ v1_relat_1(C_11)
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_1537,plain,(
    ! [B_9,B_194] :
      ( v5_relat_1('#skF_4',B_9)
      | ~ v1_relat_1('#skF_4')
      | ~ r1_tarski(B_194,B_9)
      | ~ r1_tarski('#skF_2',B_194) ) ),
    inference(resolution,[status(thm)],[c_1535,c_18])).

tff(c_1549,plain,(
    ! [B_195,B_196] :
      ( v5_relat_1('#skF_4',B_195)
      | ~ r1_tarski(B_196,B_195)
      | ~ r1_tarski('#skF_2',B_196) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_1537])).

tff(c_1559,plain,
    ( v5_relat_1('#skF_4','#skF_3')
    | ~ r1_tarski('#skF_2','#skF_2') ),
    inference(resolution,[status(thm)],[c_46,c_1549])).

tff(c_1566,plain,(
    v5_relat_1('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_1559])).

tff(c_16,plain,(
    ! [B_7,A_6] :
      ( r1_tarski(k2_relat_1(B_7),A_6)
      | ~ v5_relat_1(B_7,A_6)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_97,plain,(
    ! [C_37,A_38,B_39] :
      ( v4_relat_1(C_37,A_38)
      | ~ m1_subset_1(C_37,k1_zfmisc_1(k2_zfmisc_1(A_38,B_39))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_101,plain,(
    v4_relat_1('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_48,c_97])).

tff(c_12,plain,(
    ! [B_5,A_4] :
      ( r1_tarski(k1_relat_1(B_5),A_4)
      | ~ v4_relat_1(B_5,A_4)
      | ~ v1_relat_1(B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1664,plain,(
    ! [C_222,A_223,B_224] :
      ( m1_subset_1(C_222,k1_zfmisc_1(k2_zfmisc_1(A_223,B_224)))
      | ~ r1_tarski(k2_relat_1(C_222),B_224)
      | ~ r1_tarski(k1_relat_1(C_222),A_223)
      | ~ v1_relat_1(C_222) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_44,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_58,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_8,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_144,plain,(
    ! [C_53,B_54,A_55] :
      ( v5_relat_1(C_53,B_54)
      | ~ v5_relat_1(C_53,A_55)
      | ~ v1_relat_1(C_53)
      | ~ r1_tarski(A_55,B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_146,plain,(
    ! [B_54] :
      ( v5_relat_1('#skF_4',B_54)
      | ~ v1_relat_1('#skF_4')
      | ~ r1_tarski('#skF_2',B_54) ) ),
    inference(resolution,[status(thm)],[c_107,c_144])).

tff(c_153,plain,(
    ! [B_56] :
      ( v5_relat_1('#skF_4',B_56)
      | ~ r1_tarski('#skF_2',B_56) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_146])).

tff(c_155,plain,(
    ! [B_9,B_56] :
      ( v5_relat_1('#skF_4',B_9)
      | ~ v1_relat_1('#skF_4')
      | ~ r1_tarski(B_56,B_9)
      | ~ r1_tarski('#skF_2',B_56) ) ),
    inference(resolution,[status(thm)],[c_153,c_18])).

tff(c_167,plain,(
    ! [B_57,B_58] :
      ( v5_relat_1('#skF_4',B_57)
      | ~ r1_tarski(B_58,B_57)
      | ~ r1_tarski('#skF_2',B_58) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_155])).

tff(c_177,plain,
    ( v5_relat_1('#skF_4','#skF_3')
    | ~ r1_tarski('#skF_2','#skF_2') ),
    inference(resolution,[status(thm)],[c_46,c_167])).

tff(c_184,plain,(
    v5_relat_1('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_177])).

tff(c_50,plain,(
    v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_223,plain,(
    ! [A_65,B_66,C_67] :
      ( k1_relset_1(A_65,B_66,C_67) = k1_relat_1(C_67)
      | ~ m1_subset_1(C_67,k1_zfmisc_1(k2_zfmisc_1(A_65,B_66))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_227,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_223])).

tff(c_362,plain,(
    ! [B_95,A_96,C_97] :
      ( k1_xboole_0 = B_95
      | k1_relset_1(A_96,B_95,C_97) = A_96
      | ~ v1_funct_2(C_97,A_96,B_95)
      | ~ m1_subset_1(C_97,k1_zfmisc_1(k2_zfmisc_1(A_96,B_95))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_368,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_48,c_362])).

tff(c_372,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_227,c_368])).

tff(c_373,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_372])).

tff(c_282,plain,(
    ! [C_84,A_85,B_86] :
      ( m1_subset_1(C_84,k1_zfmisc_1(k2_zfmisc_1(A_85,B_86)))
      | ~ r1_tarski(k2_relat_1(C_84),B_86)
      | ~ r1_tarski(k1_relat_1(C_84),A_85)
      | ~ v1_relat_1(C_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_26,plain,(
    ! [A_18,B_19,C_20] :
      ( k1_relset_1(A_18,B_19,C_20) = k1_relat_1(C_20)
      | ~ m1_subset_1(C_20,k1_zfmisc_1(k2_zfmisc_1(A_18,B_19))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_319,plain,(
    ! [A_87,B_88,C_89] :
      ( k1_relset_1(A_87,B_88,C_89) = k1_relat_1(C_89)
      | ~ r1_tarski(k2_relat_1(C_89),B_88)
      | ~ r1_tarski(k1_relat_1(C_89),A_87)
      | ~ v1_relat_1(C_89) ) ),
    inference(resolution,[status(thm)],[c_282,c_26])).

tff(c_536,plain,(
    ! [A_105,A_106,B_107] :
      ( k1_relset_1(A_105,A_106,B_107) = k1_relat_1(B_107)
      | ~ r1_tarski(k1_relat_1(B_107),A_105)
      | ~ v5_relat_1(B_107,A_106)
      | ~ v1_relat_1(B_107) ) ),
    inference(resolution,[status(thm)],[c_16,c_319])).

tff(c_538,plain,(
    ! [A_105,A_106] :
      ( k1_relset_1(A_105,A_106,'#skF_4') = k1_relat_1('#skF_4')
      | ~ r1_tarski('#skF_1',A_105)
      | ~ v5_relat_1('#skF_4',A_106)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_373,c_536])).

tff(c_548,plain,(
    ! [A_108,A_109] :
      ( k1_relset_1(A_108,A_109,'#skF_4') = '#skF_1'
      | ~ r1_tarski('#skF_1',A_108)
      | ~ v5_relat_1('#skF_4',A_109) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_373,c_538])).

tff(c_553,plain,(
    ! [A_110] :
      ( k1_relset_1('#skF_1',A_110,'#skF_4') = '#skF_1'
      | ~ v5_relat_1('#skF_4',A_110) ) ),
    inference(resolution,[status(thm)],[c_6,c_548])).

tff(c_571,plain,(
    k1_relset_1('#skF_1','#skF_3','#skF_4') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_184,c_553])).

tff(c_28,plain,(
    ! [C_23,A_21,B_22] :
      ( m1_subset_1(C_23,k1_zfmisc_1(k2_zfmisc_1(A_21,B_22)))
      | ~ r1_tarski(k2_relat_1(C_23),B_22)
      | ~ r1_tarski(k1_relat_1(C_23),A_21)
      | ~ v1_relat_1(C_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_523,plain,(
    ! [B_102,C_103,A_104] :
      ( k1_xboole_0 = B_102
      | v1_funct_2(C_103,A_104,B_102)
      | k1_relset_1(A_104,B_102,C_103) != A_104
      | ~ m1_subset_1(C_103,k1_zfmisc_1(k2_zfmisc_1(A_104,B_102))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_989,plain,(
    ! [B_161,C_162,A_163] :
      ( k1_xboole_0 = B_161
      | v1_funct_2(C_162,A_163,B_161)
      | k1_relset_1(A_163,B_161,C_162) != A_163
      | ~ r1_tarski(k2_relat_1(C_162),B_161)
      | ~ r1_tarski(k1_relat_1(C_162),A_163)
      | ~ v1_relat_1(C_162) ) ),
    inference(resolution,[status(thm)],[c_28,c_523])).

tff(c_997,plain,(
    ! [A_164,B_165,A_166] :
      ( k1_xboole_0 = A_164
      | v1_funct_2(B_165,A_166,A_164)
      | k1_relset_1(A_166,A_164,B_165) != A_166
      | ~ r1_tarski(k1_relat_1(B_165),A_166)
      | ~ v5_relat_1(B_165,A_164)
      | ~ v1_relat_1(B_165) ) ),
    inference(resolution,[status(thm)],[c_16,c_989])).

tff(c_999,plain,(
    ! [A_164,A_166] :
      ( k1_xboole_0 = A_164
      | v1_funct_2('#skF_4',A_166,A_164)
      | k1_relset_1(A_166,A_164,'#skF_4') != A_166
      | ~ r1_tarski('#skF_1',A_166)
      | ~ v5_relat_1('#skF_4',A_164)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_373,c_997])).

tff(c_1009,plain,(
    ! [A_167,A_168] :
      ( k1_xboole_0 = A_167
      | v1_funct_2('#skF_4',A_168,A_167)
      | k1_relset_1(A_168,A_167,'#skF_4') != A_168
      | ~ r1_tarski('#skF_1',A_168)
      | ~ v5_relat_1('#skF_4',A_167) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_999])).

tff(c_52,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_42,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3')))
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_54,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3')))
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_42])).

tff(c_142,plain,(
    ~ v1_funct_2('#skF_4','#skF_1','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_1027,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_1','#skF_3','#skF_4') != '#skF_1'
    | ~ r1_tarski('#skF_1','#skF_1')
    | ~ v5_relat_1('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_1009,c_142])).

tff(c_1042,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_184,c_6,c_571,c_1027])).

tff(c_32,plain,(
    ! [C_26,A_24] :
      ( k1_xboole_0 = C_26
      | ~ v1_funct_2(C_26,A_24,k1_xboole_0)
      | k1_xboole_0 = A_24
      | ~ m1_subset_1(C_26,k1_zfmisc_1(k2_zfmisc_1(A_24,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_753,plain,(
    ! [C_128,A_129] :
      ( k1_xboole_0 = C_128
      | ~ v1_funct_2(C_128,A_129,k1_xboole_0)
      | k1_xboole_0 = A_129
      | ~ r1_tarski(k2_relat_1(C_128),k1_xboole_0)
      | ~ r1_tarski(k1_relat_1(C_128),A_129)
      | ~ v1_relat_1(C_128) ) ),
    inference(resolution,[status(thm)],[c_282,c_32])).

tff(c_913,plain,(
    ! [B_146,A_147] :
      ( k1_xboole_0 = B_146
      | ~ v1_funct_2(B_146,A_147,k1_xboole_0)
      | k1_xboole_0 = A_147
      | ~ r1_tarski(k1_relat_1(B_146),A_147)
      | ~ v5_relat_1(B_146,k1_xboole_0)
      | ~ v1_relat_1(B_146) ) ),
    inference(resolution,[status(thm)],[c_16,c_753])).

tff(c_916,plain,(
    ! [A_147] :
      ( k1_xboole_0 = '#skF_4'
      | ~ v1_funct_2('#skF_4',A_147,k1_xboole_0)
      | k1_xboole_0 = A_147
      | ~ r1_tarski('#skF_1',A_147)
      | ~ v5_relat_1('#skF_4',k1_xboole_0)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_373,c_913])).

tff(c_925,plain,(
    ! [A_147] :
      ( k1_xboole_0 = '#skF_4'
      | ~ v1_funct_2('#skF_4',A_147,k1_xboole_0)
      | k1_xboole_0 = A_147
      | ~ r1_tarski('#skF_1',A_147)
      | ~ v5_relat_1('#skF_4',k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_916])).

tff(c_928,plain,(
    ~ v5_relat_1('#skF_4',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_925])).

tff(c_1055,plain,(
    ~ v5_relat_1('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1042,c_928])).

tff(c_1075,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_184,c_1055])).

tff(c_1077,plain,(
    v5_relat_1('#skF_4',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_925])).

tff(c_1094,plain,(
    ! [B_9] :
      ( v5_relat_1('#skF_4',B_9)
      | ~ v1_relat_1('#skF_4')
      | ~ r1_tarski(k1_xboole_0,B_9) ) ),
    inference(resolution,[status(thm)],[c_1077,c_18])).

tff(c_1104,plain,(
    ! [B_9] : v5_relat_1('#skF_4',B_9) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_63,c_1094])).

tff(c_552,plain,(
    ! [A_109] :
      ( k1_relset_1('#skF_1',A_109,'#skF_4') = '#skF_1'
      | ~ v5_relat_1('#skF_4',A_109) ) ),
    inference(resolution,[status(thm)],[c_6,c_548])).

tff(c_1110,plain,(
    ! [A_109] : k1_relset_1('#skF_1',A_109,'#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1104,c_552])).

tff(c_118,plain,(
    ! [B_47,A_48] :
      ( r1_tarski(k2_relat_1(B_47),A_48)
      | ~ v5_relat_1(B_47,A_48)
      | ~ v1_relat_1(B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_64,plain,(
    ! [B_32,A_33] :
      ( B_32 = A_33
      | ~ r1_tarski(B_32,A_33)
      | ~ r1_tarski(A_33,B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_75,plain,(
    ! [A_3] :
      ( k1_xboole_0 = A_3
      | ~ r1_tarski(A_3,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_8,c_64])).

tff(c_129,plain,(
    ! [B_47] :
      ( k2_relat_1(B_47) = k1_xboole_0
      | ~ v5_relat_1(B_47,k1_xboole_0)
      | ~ v1_relat_1(B_47) ) ),
    inference(resolution,[status(thm)],[c_118,c_75])).

tff(c_1097,plain,
    ( k2_relat_1('#skF_4') = k1_xboole_0
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_1077,c_129])).

tff(c_1107,plain,(
    k2_relat_1('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_1097])).

tff(c_1318,plain,(
    ! [B_181,C_182,A_183] :
      ( k1_xboole_0 = B_181
      | v1_funct_2(C_182,A_183,B_181)
      | k1_relset_1(A_183,B_181,C_182) != A_183
      | ~ r1_tarski(k2_relat_1(C_182),B_181)
      | ~ r1_tarski(k1_relat_1(C_182),A_183)
      | ~ v1_relat_1(C_182) ) ),
    inference(resolution,[status(thm)],[c_28,c_523])).

tff(c_1320,plain,(
    ! [B_181,A_183] :
      ( k1_xboole_0 = B_181
      | v1_funct_2('#skF_4',A_183,B_181)
      | k1_relset_1(A_183,B_181,'#skF_4') != A_183
      | ~ r1_tarski(k1_xboole_0,B_181)
      | ~ r1_tarski(k1_relat_1('#skF_4'),A_183)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1107,c_1318])).

tff(c_1362,plain,(
    ! [B_185,A_186] :
      ( k1_xboole_0 = B_185
      | v1_funct_2('#skF_4',A_186,B_185)
      | k1_relset_1(A_186,B_185,'#skF_4') != A_186
      | ~ r1_tarski('#skF_1',A_186) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_373,c_8,c_1320])).

tff(c_1371,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_1','#skF_3','#skF_4') != '#skF_1'
    | ~ r1_tarski('#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_1362,c_142])).

tff(c_1379,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_1110,c_1371])).

tff(c_186,plain,(
    ! [B_9] :
      ( v5_relat_1('#skF_4',B_9)
      | ~ v1_relat_1('#skF_4')
      | ~ r1_tarski('#skF_3',B_9) ) ),
    inference(resolution,[status(thm)],[c_184,c_18])).

tff(c_190,plain,(
    ! [B_59] :
      ( v5_relat_1('#skF_4',B_59)
      | ~ r1_tarski('#skF_3',B_59) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_186])).

tff(c_196,plain,
    ( k2_relat_1('#skF_4') = k1_xboole_0
    | ~ v1_relat_1('#skF_4')
    | ~ r1_tarski('#skF_3',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_190,c_129])).

tff(c_202,plain,
    ( k2_relat_1('#skF_4') = k1_xboole_0
    | ~ r1_tarski('#skF_3',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_196])).

tff(c_204,plain,(
    ~ r1_tarski('#skF_3',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_202])).

tff(c_1410,plain,(
    ~ r1_tarski('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1379,c_204])).

tff(c_1420,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_1410])).

tff(c_1422,plain,(
    r1_tarski('#skF_3',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_202])).

tff(c_1452,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_1422,c_75])).

tff(c_159,plain,
    ( k2_relat_1('#skF_4') = k1_xboole_0
    | ~ v1_relat_1('#skF_4')
    | ~ r1_tarski('#skF_2',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_153,c_129])).

tff(c_165,plain,
    ( k2_relat_1('#skF_4') = k1_xboole_0
    | ~ r1_tarski('#skF_2',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_159])).

tff(c_166,plain,(
    ~ r1_tarski('#skF_2',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_165])).

tff(c_1483,plain,(
    ~ r1_tarski('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1452,c_166])).

tff(c_1492,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_1483])).

tff(c_1494,plain,(
    r1_tarski('#skF_2',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_165])).

tff(c_1516,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_1494,c_75])).

tff(c_1522,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_1516])).

tff(c_1523,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_1686,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_3')
    | ~ r1_tarski(k1_relat_1('#skF_4'),'#skF_1')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_1664,c_1523])).

tff(c_1703,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_3')
    | ~ r1_tarski(k1_relat_1('#skF_4'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_1686])).

tff(c_1707,plain,(
    ~ r1_tarski(k1_relat_1('#skF_4'),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_1703])).

tff(c_1710,plain,
    ( ~ v4_relat_1('#skF_4','#skF_1')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_12,c_1707])).

tff(c_1714,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_101,c_1710])).

tff(c_1715,plain,(
    ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_1703])).

tff(c_1734,plain,
    ( ~ v5_relat_1('#skF_4','#skF_3')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_16,c_1715])).

tff(c_1738,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_1566,c_1734])).

tff(c_1739,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_1740,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_1746,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1739,c_1740])).

tff(c_1755,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1746,c_48])).

tff(c_1779,plain,(
    ! [C_229,A_230,B_231] :
      ( v1_relat_1(C_229)
      | ~ m1_subset_1(C_229,k1_zfmisc_1(k2_zfmisc_1(A_230,B_231))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_1783,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_1755,c_1779])).

tff(c_1741,plain,(
    ! [A_3] : r1_tarski('#skF_1',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1739,c_8])).

tff(c_2402,plain,(
    ! [C_314,A_315,B_316] :
      ( v4_relat_1(C_314,A_315)
      | ~ m1_subset_1(C_314,k1_zfmisc_1(k2_zfmisc_1(A_315,B_316))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_2406,plain,(
    v4_relat_1('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_1755,c_2402])).

tff(c_2407,plain,(
    ! [B_317,A_318] :
      ( r1_tarski(k1_relat_1(B_317),A_318)
      | ~ v4_relat_1(B_317,A_318)
      | ~ v1_relat_1(B_317) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1756,plain,(
    ! [B_226,A_227] :
      ( B_226 = A_227
      | ~ r1_tarski(B_226,A_227)
      | ~ r1_tarski(A_227,B_226) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1761,plain,(
    ! [A_3] :
      ( A_3 = '#skF_1'
      | ~ r1_tarski(A_3,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_1741,c_1756])).

tff(c_2420,plain,(
    ! [B_319] :
      ( k1_relat_1(B_319) = '#skF_1'
      | ~ v4_relat_1(B_319,'#skF_1')
      | ~ v1_relat_1(B_319) ) ),
    inference(resolution,[status(thm)],[c_2407,c_1761])).

tff(c_2423,plain,
    ( k1_relat_1('#skF_4') = '#skF_1'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_2406,c_2420])).

tff(c_2426,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1783,c_2423])).

tff(c_1805,plain,(
    ! [C_238,B_239,A_240] :
      ( v5_relat_1(C_238,B_239)
      | ~ m1_subset_1(C_238,k1_zfmisc_1(k2_zfmisc_1(A_240,B_239))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_1809,plain,(
    v5_relat_1('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_1755,c_1805])).

tff(c_1784,plain,(
    ! [B_232,A_233] :
      ( r1_tarski(k2_relat_1(B_232),A_233)
      | ~ v5_relat_1(B_232,A_233)
      | ~ v1_relat_1(B_232) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1791,plain,(
    ! [B_232] :
      ( k2_relat_1(B_232) = '#skF_1'
      | ~ v5_relat_1(B_232,'#skF_1')
      | ~ v1_relat_1(B_232) ) ),
    inference(resolution,[status(thm)],[c_1784,c_1761])).

tff(c_2363,plain,
    ( k2_relat_1('#skF_4') = '#skF_1'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_1809,c_1791])).

tff(c_2366,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1783,c_2363])).

tff(c_2555,plain,(
    ! [C_338,A_339,B_340] :
      ( m1_subset_1(C_338,k1_zfmisc_1(k2_zfmisc_1(A_339,B_340)))
      | ~ r1_tarski(k2_relat_1(C_338),B_340)
      | ~ r1_tarski(k1_relat_1(C_338),A_339)
      | ~ v1_relat_1(C_338) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_1845,plain,(
    ! [C_242,A_243,B_244] :
      ( v4_relat_1(C_242,A_243)
      | ~ m1_subset_1(C_242,k1_zfmisc_1(k2_zfmisc_1(A_243,B_244))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_1849,plain,(
    v4_relat_1('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_1755,c_1845])).

tff(c_1857,plain,(
    ! [B_248,A_249] :
      ( r1_tarski(k1_relat_1(B_248),A_249)
      | ~ v4_relat_1(B_248,A_249)
      | ~ v1_relat_1(B_248) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1879,plain,(
    ! [B_253] :
      ( k1_relat_1(B_253) = '#skF_1'
      | ~ v4_relat_1(B_253,'#skF_1')
      | ~ v1_relat_1(B_253) ) ),
    inference(resolution,[status(thm)],[c_1857,c_1761])).

tff(c_1882,plain,
    ( k1_relat_1('#skF_4') = '#skF_1'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_1849,c_1879])).

tff(c_1885,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1783,c_1882])).

tff(c_1813,plain,
    ( k2_relat_1('#skF_4') = '#skF_1'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_1809,c_1791])).

tff(c_1816,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1783,c_1813])).

tff(c_2005,plain,(
    ! [C_269,A_270,B_271] :
      ( m1_subset_1(C_269,k1_zfmisc_1(k2_zfmisc_1(A_270,B_271)))
      | ~ r1_tarski(k2_relat_1(C_269),B_271)
      | ~ r1_tarski(k1_relat_1(C_269),A_270)
      | ~ v1_relat_1(C_269) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_2043,plain,(
    ! [A_272,B_273,C_274] :
      ( k1_relset_1(A_272,B_273,C_274) = k1_relat_1(C_274)
      | ~ r1_tarski(k2_relat_1(C_274),B_273)
      | ~ r1_tarski(k1_relat_1(C_274),A_272)
      | ~ v1_relat_1(C_274) ) ),
    inference(resolution,[status(thm)],[c_2005,c_26])).

tff(c_2045,plain,(
    ! [A_272,B_273] :
      ( k1_relset_1(A_272,B_273,'#skF_4') = k1_relat_1('#skF_4')
      | ~ r1_tarski('#skF_1',B_273)
      | ~ r1_tarski(k1_relat_1('#skF_4'),A_272)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1816,c_2043])).

tff(c_2052,plain,(
    ! [A_272,B_273] : k1_relset_1(A_272,B_273,'#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1783,c_1741,c_1885,c_1741,c_1885,c_2045])).

tff(c_34,plain,(
    ! [C_26,B_25] :
      ( v1_funct_2(C_26,k1_xboole_0,B_25)
      | k1_relset_1(k1_xboole_0,B_25,C_26) != k1_xboole_0
      | ~ m1_subset_1(C_26,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_25))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_1997,plain,(
    ! [C_26,B_25] :
      ( v1_funct_2(C_26,'#skF_1',B_25)
      | k1_relset_1('#skF_1',B_25,C_26) != '#skF_1'
      | ~ m1_subset_1(C_26,k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_25))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1739,c_1739,c_1739,c_1739,c_34])).

tff(c_2340,plain,(
    ! [C_308,B_309] :
      ( v1_funct_2(C_308,'#skF_1',B_309)
      | k1_relset_1('#skF_1',B_309,C_308) != '#skF_1'
      | ~ r1_tarski(k2_relat_1(C_308),B_309)
      | ~ r1_tarski(k1_relat_1(C_308),'#skF_1')
      | ~ v1_relat_1(C_308) ) ),
    inference(resolution,[status(thm)],[c_2005,c_1997])).

tff(c_2343,plain,(
    ! [B_309] :
      ( v1_funct_2('#skF_4','#skF_1',B_309)
      | k1_relset_1('#skF_1',B_309,'#skF_4') != '#skF_1'
      | ~ r1_tarski('#skF_1',B_309)
      | ~ r1_tarski(k1_relat_1('#skF_4'),'#skF_1')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1816,c_2340])).

tff(c_2352,plain,(
    ! [B_309] : v1_funct_2('#skF_4','#skF_1',B_309) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1783,c_1741,c_1885,c_1741,c_2052,c_2343])).

tff(c_1810,plain,(
    ~ v1_funct_2('#skF_4','#skF_1','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_2358,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2352,c_1810])).

tff(c_2359,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_2580,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_3')
    | ~ r1_tarski(k1_relat_1('#skF_4'),'#skF_1')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_2555,c_2359])).

tff(c_2596,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1783,c_1741,c_2426,c_1741,c_2366,c_2580])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n012.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 10:39:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.27/1.77  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.27/1.80  
% 4.27/1.80  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.27/1.81  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 4.27/1.81  
% 4.27/1.81  %Foreground sorts:
% 4.27/1.81  
% 4.27/1.81  
% 4.27/1.81  %Background operators:
% 4.27/1.81  
% 4.27/1.81  
% 4.27/1.81  %Foreground operators:
% 4.27/1.81  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.27/1.81  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.27/1.81  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.27/1.81  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.27/1.81  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.27/1.81  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.27/1.81  tff('#skF_2', type, '#skF_2': $i).
% 4.27/1.81  tff('#skF_3', type, '#skF_3': $i).
% 4.27/1.81  tff('#skF_1', type, '#skF_1': $i).
% 4.27/1.81  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 4.27/1.81  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 4.27/1.81  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.27/1.81  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.27/1.81  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.27/1.81  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.27/1.81  tff('#skF_4', type, '#skF_4': $i).
% 4.27/1.81  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.27/1.81  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 4.27/1.81  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.27/1.81  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.27/1.81  
% 4.56/1.83  tff(f_114, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_tarski(B, C) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | ((v1_funct_1(D) & v1_funct_2(D, A, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_funct_2)).
% 4.56/1.83  tff(f_58, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 4.56/1.83  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.56/1.83  tff(f_64, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 4.56/1.83  tff(f_54, axiom, (![A, B]: (r1_tarski(A, B) => (![C]: ((v1_relat_1(C) & v5_relat_1(C, A)) => v5_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t218_relat_1)).
% 4.56/1.83  tff(f_45, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 4.56/1.83  tff(f_39, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 4.56/1.83  tff(f_76, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_relset_1)).
% 4.56/1.83  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 4.56/1.83  tff(f_68, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 4.56/1.83  tff(f_94, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 4.56/1.83  tff(c_48, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_114])).
% 4.56/1.83  tff(c_59, plain, (![C_29, A_30, B_31]: (v1_relat_1(C_29) | ~m1_subset_1(C_29, k1_zfmisc_1(k2_zfmisc_1(A_30, B_31))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.56/1.83  tff(c_63, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_48, c_59])).
% 4.56/1.83  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.56/1.83  tff(c_46, plain, (r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_114])).
% 4.56/1.83  tff(c_103, plain, (![C_41, B_42, A_43]: (v5_relat_1(C_41, B_42) | ~m1_subset_1(C_41, k1_zfmisc_1(k2_zfmisc_1(A_43, B_42))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.56/1.83  tff(c_107, plain, (v5_relat_1('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_48, c_103])).
% 4.56/1.83  tff(c_1525, plain, (![C_190, B_191, A_192]: (v5_relat_1(C_190, B_191) | ~v5_relat_1(C_190, A_192) | ~v1_relat_1(C_190) | ~r1_tarski(A_192, B_191))), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.56/1.83  tff(c_1527, plain, (![B_191]: (v5_relat_1('#skF_4', B_191) | ~v1_relat_1('#skF_4') | ~r1_tarski('#skF_2', B_191))), inference(resolution, [status(thm)], [c_107, c_1525])).
% 4.56/1.83  tff(c_1535, plain, (![B_194]: (v5_relat_1('#skF_4', B_194) | ~r1_tarski('#skF_2', B_194))), inference(demodulation, [status(thm), theory('equality')], [c_63, c_1527])).
% 4.56/1.83  tff(c_18, plain, (![C_11, B_9, A_8]: (v5_relat_1(C_11, B_9) | ~v5_relat_1(C_11, A_8) | ~v1_relat_1(C_11) | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.56/1.83  tff(c_1537, plain, (![B_9, B_194]: (v5_relat_1('#skF_4', B_9) | ~v1_relat_1('#skF_4') | ~r1_tarski(B_194, B_9) | ~r1_tarski('#skF_2', B_194))), inference(resolution, [status(thm)], [c_1535, c_18])).
% 4.56/1.83  tff(c_1549, plain, (![B_195, B_196]: (v5_relat_1('#skF_4', B_195) | ~r1_tarski(B_196, B_195) | ~r1_tarski('#skF_2', B_196))), inference(demodulation, [status(thm), theory('equality')], [c_63, c_1537])).
% 4.56/1.83  tff(c_1559, plain, (v5_relat_1('#skF_4', '#skF_3') | ~r1_tarski('#skF_2', '#skF_2')), inference(resolution, [status(thm)], [c_46, c_1549])).
% 4.56/1.83  tff(c_1566, plain, (v5_relat_1('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_1559])).
% 4.56/1.83  tff(c_16, plain, (![B_7, A_6]: (r1_tarski(k2_relat_1(B_7), A_6) | ~v5_relat_1(B_7, A_6) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.56/1.83  tff(c_97, plain, (![C_37, A_38, B_39]: (v4_relat_1(C_37, A_38) | ~m1_subset_1(C_37, k1_zfmisc_1(k2_zfmisc_1(A_38, B_39))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.56/1.83  tff(c_101, plain, (v4_relat_1('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_48, c_97])).
% 4.56/1.83  tff(c_12, plain, (![B_5, A_4]: (r1_tarski(k1_relat_1(B_5), A_4) | ~v4_relat_1(B_5, A_4) | ~v1_relat_1(B_5))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.56/1.83  tff(c_1664, plain, (![C_222, A_223, B_224]: (m1_subset_1(C_222, k1_zfmisc_1(k2_zfmisc_1(A_223, B_224))) | ~r1_tarski(k2_relat_1(C_222), B_224) | ~r1_tarski(k1_relat_1(C_222), A_223) | ~v1_relat_1(C_222))), inference(cnfTransformation, [status(thm)], [f_76])).
% 4.56/1.83  tff(c_44, plain, (k1_xboole_0='#skF_1' | k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_114])).
% 4.56/1.83  tff(c_58, plain, (k1_xboole_0!='#skF_2'), inference(splitLeft, [status(thm)], [c_44])).
% 4.56/1.83  tff(c_8, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.56/1.83  tff(c_144, plain, (![C_53, B_54, A_55]: (v5_relat_1(C_53, B_54) | ~v5_relat_1(C_53, A_55) | ~v1_relat_1(C_53) | ~r1_tarski(A_55, B_54))), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.56/1.83  tff(c_146, plain, (![B_54]: (v5_relat_1('#skF_4', B_54) | ~v1_relat_1('#skF_4') | ~r1_tarski('#skF_2', B_54))), inference(resolution, [status(thm)], [c_107, c_144])).
% 4.56/1.83  tff(c_153, plain, (![B_56]: (v5_relat_1('#skF_4', B_56) | ~r1_tarski('#skF_2', B_56))), inference(demodulation, [status(thm), theory('equality')], [c_63, c_146])).
% 4.56/1.83  tff(c_155, plain, (![B_9, B_56]: (v5_relat_1('#skF_4', B_9) | ~v1_relat_1('#skF_4') | ~r1_tarski(B_56, B_9) | ~r1_tarski('#skF_2', B_56))), inference(resolution, [status(thm)], [c_153, c_18])).
% 4.56/1.83  tff(c_167, plain, (![B_57, B_58]: (v5_relat_1('#skF_4', B_57) | ~r1_tarski(B_58, B_57) | ~r1_tarski('#skF_2', B_58))), inference(demodulation, [status(thm), theory('equality')], [c_63, c_155])).
% 4.56/1.83  tff(c_177, plain, (v5_relat_1('#skF_4', '#skF_3') | ~r1_tarski('#skF_2', '#skF_2')), inference(resolution, [status(thm)], [c_46, c_167])).
% 4.56/1.83  tff(c_184, plain, (v5_relat_1('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_177])).
% 4.56/1.83  tff(c_50, plain, (v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_114])).
% 4.56/1.83  tff(c_223, plain, (![A_65, B_66, C_67]: (k1_relset_1(A_65, B_66, C_67)=k1_relat_1(C_67) | ~m1_subset_1(C_67, k1_zfmisc_1(k2_zfmisc_1(A_65, B_66))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 4.56/1.83  tff(c_227, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_48, c_223])).
% 4.56/1.83  tff(c_362, plain, (![B_95, A_96, C_97]: (k1_xboole_0=B_95 | k1_relset_1(A_96, B_95, C_97)=A_96 | ~v1_funct_2(C_97, A_96, B_95) | ~m1_subset_1(C_97, k1_zfmisc_1(k2_zfmisc_1(A_96, B_95))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 4.56/1.83  tff(c_368, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_1' | ~v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_48, c_362])).
% 4.56/1.83  tff(c_372, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_50, c_227, c_368])).
% 4.56/1.83  tff(c_373, plain, (k1_relat_1('#skF_4')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_58, c_372])).
% 4.56/1.83  tff(c_282, plain, (![C_84, A_85, B_86]: (m1_subset_1(C_84, k1_zfmisc_1(k2_zfmisc_1(A_85, B_86))) | ~r1_tarski(k2_relat_1(C_84), B_86) | ~r1_tarski(k1_relat_1(C_84), A_85) | ~v1_relat_1(C_84))), inference(cnfTransformation, [status(thm)], [f_76])).
% 4.56/1.83  tff(c_26, plain, (![A_18, B_19, C_20]: (k1_relset_1(A_18, B_19, C_20)=k1_relat_1(C_20) | ~m1_subset_1(C_20, k1_zfmisc_1(k2_zfmisc_1(A_18, B_19))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 4.56/1.83  tff(c_319, plain, (![A_87, B_88, C_89]: (k1_relset_1(A_87, B_88, C_89)=k1_relat_1(C_89) | ~r1_tarski(k2_relat_1(C_89), B_88) | ~r1_tarski(k1_relat_1(C_89), A_87) | ~v1_relat_1(C_89))), inference(resolution, [status(thm)], [c_282, c_26])).
% 4.56/1.83  tff(c_536, plain, (![A_105, A_106, B_107]: (k1_relset_1(A_105, A_106, B_107)=k1_relat_1(B_107) | ~r1_tarski(k1_relat_1(B_107), A_105) | ~v5_relat_1(B_107, A_106) | ~v1_relat_1(B_107))), inference(resolution, [status(thm)], [c_16, c_319])).
% 4.56/1.83  tff(c_538, plain, (![A_105, A_106]: (k1_relset_1(A_105, A_106, '#skF_4')=k1_relat_1('#skF_4') | ~r1_tarski('#skF_1', A_105) | ~v5_relat_1('#skF_4', A_106) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_373, c_536])).
% 4.56/1.83  tff(c_548, plain, (![A_108, A_109]: (k1_relset_1(A_108, A_109, '#skF_4')='#skF_1' | ~r1_tarski('#skF_1', A_108) | ~v5_relat_1('#skF_4', A_109))), inference(demodulation, [status(thm), theory('equality')], [c_63, c_373, c_538])).
% 4.56/1.83  tff(c_553, plain, (![A_110]: (k1_relset_1('#skF_1', A_110, '#skF_4')='#skF_1' | ~v5_relat_1('#skF_4', A_110))), inference(resolution, [status(thm)], [c_6, c_548])).
% 4.56/1.83  tff(c_571, plain, (k1_relset_1('#skF_1', '#skF_3', '#skF_4')='#skF_1'), inference(resolution, [status(thm)], [c_184, c_553])).
% 4.56/1.83  tff(c_28, plain, (![C_23, A_21, B_22]: (m1_subset_1(C_23, k1_zfmisc_1(k2_zfmisc_1(A_21, B_22))) | ~r1_tarski(k2_relat_1(C_23), B_22) | ~r1_tarski(k1_relat_1(C_23), A_21) | ~v1_relat_1(C_23))), inference(cnfTransformation, [status(thm)], [f_76])).
% 4.56/1.83  tff(c_523, plain, (![B_102, C_103, A_104]: (k1_xboole_0=B_102 | v1_funct_2(C_103, A_104, B_102) | k1_relset_1(A_104, B_102, C_103)!=A_104 | ~m1_subset_1(C_103, k1_zfmisc_1(k2_zfmisc_1(A_104, B_102))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 4.56/1.83  tff(c_989, plain, (![B_161, C_162, A_163]: (k1_xboole_0=B_161 | v1_funct_2(C_162, A_163, B_161) | k1_relset_1(A_163, B_161, C_162)!=A_163 | ~r1_tarski(k2_relat_1(C_162), B_161) | ~r1_tarski(k1_relat_1(C_162), A_163) | ~v1_relat_1(C_162))), inference(resolution, [status(thm)], [c_28, c_523])).
% 4.56/1.83  tff(c_997, plain, (![A_164, B_165, A_166]: (k1_xboole_0=A_164 | v1_funct_2(B_165, A_166, A_164) | k1_relset_1(A_166, A_164, B_165)!=A_166 | ~r1_tarski(k1_relat_1(B_165), A_166) | ~v5_relat_1(B_165, A_164) | ~v1_relat_1(B_165))), inference(resolution, [status(thm)], [c_16, c_989])).
% 4.56/1.83  tff(c_999, plain, (![A_164, A_166]: (k1_xboole_0=A_164 | v1_funct_2('#skF_4', A_166, A_164) | k1_relset_1(A_166, A_164, '#skF_4')!=A_166 | ~r1_tarski('#skF_1', A_166) | ~v5_relat_1('#skF_4', A_164) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_373, c_997])).
% 4.56/1.83  tff(c_1009, plain, (![A_167, A_168]: (k1_xboole_0=A_167 | v1_funct_2('#skF_4', A_168, A_167) | k1_relset_1(A_168, A_167, '#skF_4')!=A_168 | ~r1_tarski('#skF_1', A_168) | ~v5_relat_1('#skF_4', A_167))), inference(demodulation, [status(thm), theory('equality')], [c_63, c_999])).
% 4.56/1.83  tff(c_52, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_114])).
% 4.56/1.83  tff(c_42, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3'))) | ~v1_funct_2('#skF_4', '#skF_1', '#skF_3') | ~v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_114])).
% 4.56/1.83  tff(c_54, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3'))) | ~v1_funct_2('#skF_4', '#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_42])).
% 4.56/1.83  tff(c_142, plain, (~v1_funct_2('#skF_4', '#skF_1', '#skF_3')), inference(splitLeft, [status(thm)], [c_54])).
% 4.56/1.83  tff(c_1027, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_1', '#skF_3', '#skF_4')!='#skF_1' | ~r1_tarski('#skF_1', '#skF_1') | ~v5_relat_1('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_1009, c_142])).
% 4.56/1.83  tff(c_1042, plain, (k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_184, c_6, c_571, c_1027])).
% 4.56/1.83  tff(c_32, plain, (![C_26, A_24]: (k1_xboole_0=C_26 | ~v1_funct_2(C_26, A_24, k1_xboole_0) | k1_xboole_0=A_24 | ~m1_subset_1(C_26, k1_zfmisc_1(k2_zfmisc_1(A_24, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 4.56/1.83  tff(c_753, plain, (![C_128, A_129]: (k1_xboole_0=C_128 | ~v1_funct_2(C_128, A_129, k1_xboole_0) | k1_xboole_0=A_129 | ~r1_tarski(k2_relat_1(C_128), k1_xboole_0) | ~r1_tarski(k1_relat_1(C_128), A_129) | ~v1_relat_1(C_128))), inference(resolution, [status(thm)], [c_282, c_32])).
% 4.56/1.83  tff(c_913, plain, (![B_146, A_147]: (k1_xboole_0=B_146 | ~v1_funct_2(B_146, A_147, k1_xboole_0) | k1_xboole_0=A_147 | ~r1_tarski(k1_relat_1(B_146), A_147) | ~v5_relat_1(B_146, k1_xboole_0) | ~v1_relat_1(B_146))), inference(resolution, [status(thm)], [c_16, c_753])).
% 4.56/1.83  tff(c_916, plain, (![A_147]: (k1_xboole_0='#skF_4' | ~v1_funct_2('#skF_4', A_147, k1_xboole_0) | k1_xboole_0=A_147 | ~r1_tarski('#skF_1', A_147) | ~v5_relat_1('#skF_4', k1_xboole_0) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_373, c_913])).
% 4.56/1.83  tff(c_925, plain, (![A_147]: (k1_xboole_0='#skF_4' | ~v1_funct_2('#skF_4', A_147, k1_xboole_0) | k1_xboole_0=A_147 | ~r1_tarski('#skF_1', A_147) | ~v5_relat_1('#skF_4', k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_63, c_916])).
% 4.56/1.83  tff(c_928, plain, (~v5_relat_1('#skF_4', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_925])).
% 4.56/1.83  tff(c_1055, plain, (~v5_relat_1('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1042, c_928])).
% 4.56/1.83  tff(c_1075, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_184, c_1055])).
% 4.56/1.83  tff(c_1077, plain, (v5_relat_1('#skF_4', k1_xboole_0)), inference(splitRight, [status(thm)], [c_925])).
% 4.56/1.83  tff(c_1094, plain, (![B_9]: (v5_relat_1('#skF_4', B_9) | ~v1_relat_1('#skF_4') | ~r1_tarski(k1_xboole_0, B_9))), inference(resolution, [status(thm)], [c_1077, c_18])).
% 4.56/1.83  tff(c_1104, plain, (![B_9]: (v5_relat_1('#skF_4', B_9))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_63, c_1094])).
% 4.56/1.83  tff(c_552, plain, (![A_109]: (k1_relset_1('#skF_1', A_109, '#skF_4')='#skF_1' | ~v5_relat_1('#skF_4', A_109))), inference(resolution, [status(thm)], [c_6, c_548])).
% 4.56/1.83  tff(c_1110, plain, (![A_109]: (k1_relset_1('#skF_1', A_109, '#skF_4')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1104, c_552])).
% 4.56/1.83  tff(c_118, plain, (![B_47, A_48]: (r1_tarski(k2_relat_1(B_47), A_48) | ~v5_relat_1(B_47, A_48) | ~v1_relat_1(B_47))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.56/1.83  tff(c_64, plain, (![B_32, A_33]: (B_32=A_33 | ~r1_tarski(B_32, A_33) | ~r1_tarski(A_33, B_32))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.56/1.83  tff(c_75, plain, (![A_3]: (k1_xboole_0=A_3 | ~r1_tarski(A_3, k1_xboole_0))), inference(resolution, [status(thm)], [c_8, c_64])).
% 4.56/1.83  tff(c_129, plain, (![B_47]: (k2_relat_1(B_47)=k1_xboole_0 | ~v5_relat_1(B_47, k1_xboole_0) | ~v1_relat_1(B_47))), inference(resolution, [status(thm)], [c_118, c_75])).
% 4.56/1.83  tff(c_1097, plain, (k2_relat_1('#skF_4')=k1_xboole_0 | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_1077, c_129])).
% 4.56/1.83  tff(c_1107, plain, (k2_relat_1('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_63, c_1097])).
% 4.56/1.83  tff(c_1318, plain, (![B_181, C_182, A_183]: (k1_xboole_0=B_181 | v1_funct_2(C_182, A_183, B_181) | k1_relset_1(A_183, B_181, C_182)!=A_183 | ~r1_tarski(k2_relat_1(C_182), B_181) | ~r1_tarski(k1_relat_1(C_182), A_183) | ~v1_relat_1(C_182))), inference(resolution, [status(thm)], [c_28, c_523])).
% 4.56/1.83  tff(c_1320, plain, (![B_181, A_183]: (k1_xboole_0=B_181 | v1_funct_2('#skF_4', A_183, B_181) | k1_relset_1(A_183, B_181, '#skF_4')!=A_183 | ~r1_tarski(k1_xboole_0, B_181) | ~r1_tarski(k1_relat_1('#skF_4'), A_183) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1107, c_1318])).
% 4.56/1.83  tff(c_1362, plain, (![B_185, A_186]: (k1_xboole_0=B_185 | v1_funct_2('#skF_4', A_186, B_185) | k1_relset_1(A_186, B_185, '#skF_4')!=A_186 | ~r1_tarski('#skF_1', A_186))), inference(demodulation, [status(thm), theory('equality')], [c_63, c_373, c_8, c_1320])).
% 4.56/1.83  tff(c_1371, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_1', '#skF_3', '#skF_4')!='#skF_1' | ~r1_tarski('#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_1362, c_142])).
% 4.56/1.83  tff(c_1379, plain, (k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_6, c_1110, c_1371])).
% 4.56/1.83  tff(c_186, plain, (![B_9]: (v5_relat_1('#skF_4', B_9) | ~v1_relat_1('#skF_4') | ~r1_tarski('#skF_3', B_9))), inference(resolution, [status(thm)], [c_184, c_18])).
% 4.56/1.83  tff(c_190, plain, (![B_59]: (v5_relat_1('#skF_4', B_59) | ~r1_tarski('#skF_3', B_59))), inference(demodulation, [status(thm), theory('equality')], [c_63, c_186])).
% 4.56/1.83  tff(c_196, plain, (k2_relat_1('#skF_4')=k1_xboole_0 | ~v1_relat_1('#skF_4') | ~r1_tarski('#skF_3', k1_xboole_0)), inference(resolution, [status(thm)], [c_190, c_129])).
% 4.56/1.83  tff(c_202, plain, (k2_relat_1('#skF_4')=k1_xboole_0 | ~r1_tarski('#skF_3', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_63, c_196])).
% 4.56/1.83  tff(c_204, plain, (~r1_tarski('#skF_3', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_202])).
% 4.56/1.83  tff(c_1410, plain, (~r1_tarski('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1379, c_204])).
% 4.56/1.83  tff(c_1420, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_1410])).
% 4.56/1.83  tff(c_1422, plain, (r1_tarski('#skF_3', k1_xboole_0)), inference(splitRight, [status(thm)], [c_202])).
% 4.56/1.83  tff(c_1452, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_1422, c_75])).
% 4.56/1.83  tff(c_159, plain, (k2_relat_1('#skF_4')=k1_xboole_0 | ~v1_relat_1('#skF_4') | ~r1_tarski('#skF_2', k1_xboole_0)), inference(resolution, [status(thm)], [c_153, c_129])).
% 4.56/1.83  tff(c_165, plain, (k2_relat_1('#skF_4')=k1_xboole_0 | ~r1_tarski('#skF_2', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_63, c_159])).
% 4.56/1.83  tff(c_166, plain, (~r1_tarski('#skF_2', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_165])).
% 4.56/1.83  tff(c_1483, plain, (~r1_tarski('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1452, c_166])).
% 4.56/1.83  tff(c_1492, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_1483])).
% 4.56/1.83  tff(c_1494, plain, (r1_tarski('#skF_2', k1_xboole_0)), inference(splitRight, [status(thm)], [c_165])).
% 4.56/1.83  tff(c_1516, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_1494, c_75])).
% 4.56/1.83  tff(c_1522, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_1516])).
% 4.56/1.83  tff(c_1523, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3')))), inference(splitRight, [status(thm)], [c_54])).
% 4.56/1.83  tff(c_1686, plain, (~r1_tarski(k2_relat_1('#skF_4'), '#skF_3') | ~r1_tarski(k1_relat_1('#skF_4'), '#skF_1') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_1664, c_1523])).
% 4.56/1.83  tff(c_1703, plain, (~r1_tarski(k2_relat_1('#skF_4'), '#skF_3') | ~r1_tarski(k1_relat_1('#skF_4'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_63, c_1686])).
% 4.56/1.83  tff(c_1707, plain, (~r1_tarski(k1_relat_1('#skF_4'), '#skF_1')), inference(splitLeft, [status(thm)], [c_1703])).
% 4.56/1.83  tff(c_1710, plain, (~v4_relat_1('#skF_4', '#skF_1') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_12, c_1707])).
% 4.56/1.83  tff(c_1714, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_63, c_101, c_1710])).
% 4.56/1.83  tff(c_1715, plain, (~r1_tarski(k2_relat_1('#skF_4'), '#skF_3')), inference(splitRight, [status(thm)], [c_1703])).
% 4.56/1.83  tff(c_1734, plain, (~v5_relat_1('#skF_4', '#skF_3') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_16, c_1715])).
% 4.56/1.83  tff(c_1738, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_63, c_1566, c_1734])).
% 4.56/1.83  tff(c_1739, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_44])).
% 4.56/1.83  tff(c_1740, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_44])).
% 4.56/1.83  tff(c_1746, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1739, c_1740])).
% 4.56/1.83  tff(c_1755, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_1746, c_48])).
% 4.56/1.83  tff(c_1779, plain, (![C_229, A_230, B_231]: (v1_relat_1(C_229) | ~m1_subset_1(C_229, k1_zfmisc_1(k2_zfmisc_1(A_230, B_231))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.56/1.83  tff(c_1783, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_1755, c_1779])).
% 4.56/1.83  tff(c_1741, plain, (![A_3]: (r1_tarski('#skF_1', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_1739, c_8])).
% 4.56/1.83  tff(c_2402, plain, (![C_314, A_315, B_316]: (v4_relat_1(C_314, A_315) | ~m1_subset_1(C_314, k1_zfmisc_1(k2_zfmisc_1(A_315, B_316))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.56/1.83  tff(c_2406, plain, (v4_relat_1('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_1755, c_2402])).
% 4.56/1.83  tff(c_2407, plain, (![B_317, A_318]: (r1_tarski(k1_relat_1(B_317), A_318) | ~v4_relat_1(B_317, A_318) | ~v1_relat_1(B_317))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.56/1.83  tff(c_1756, plain, (![B_226, A_227]: (B_226=A_227 | ~r1_tarski(B_226, A_227) | ~r1_tarski(A_227, B_226))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.56/1.83  tff(c_1761, plain, (![A_3]: (A_3='#skF_1' | ~r1_tarski(A_3, '#skF_1'))), inference(resolution, [status(thm)], [c_1741, c_1756])).
% 4.56/1.83  tff(c_2420, plain, (![B_319]: (k1_relat_1(B_319)='#skF_1' | ~v4_relat_1(B_319, '#skF_1') | ~v1_relat_1(B_319))), inference(resolution, [status(thm)], [c_2407, c_1761])).
% 4.56/1.83  tff(c_2423, plain, (k1_relat_1('#skF_4')='#skF_1' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_2406, c_2420])).
% 4.56/1.83  tff(c_2426, plain, (k1_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1783, c_2423])).
% 4.56/1.83  tff(c_1805, plain, (![C_238, B_239, A_240]: (v5_relat_1(C_238, B_239) | ~m1_subset_1(C_238, k1_zfmisc_1(k2_zfmisc_1(A_240, B_239))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.56/1.83  tff(c_1809, plain, (v5_relat_1('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_1755, c_1805])).
% 4.56/1.83  tff(c_1784, plain, (![B_232, A_233]: (r1_tarski(k2_relat_1(B_232), A_233) | ~v5_relat_1(B_232, A_233) | ~v1_relat_1(B_232))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.56/1.83  tff(c_1791, plain, (![B_232]: (k2_relat_1(B_232)='#skF_1' | ~v5_relat_1(B_232, '#skF_1') | ~v1_relat_1(B_232))), inference(resolution, [status(thm)], [c_1784, c_1761])).
% 4.56/1.83  tff(c_2363, plain, (k2_relat_1('#skF_4')='#skF_1' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_1809, c_1791])).
% 4.56/1.83  tff(c_2366, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1783, c_2363])).
% 4.56/1.83  tff(c_2555, plain, (![C_338, A_339, B_340]: (m1_subset_1(C_338, k1_zfmisc_1(k2_zfmisc_1(A_339, B_340))) | ~r1_tarski(k2_relat_1(C_338), B_340) | ~r1_tarski(k1_relat_1(C_338), A_339) | ~v1_relat_1(C_338))), inference(cnfTransformation, [status(thm)], [f_76])).
% 4.56/1.83  tff(c_1845, plain, (![C_242, A_243, B_244]: (v4_relat_1(C_242, A_243) | ~m1_subset_1(C_242, k1_zfmisc_1(k2_zfmisc_1(A_243, B_244))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.56/1.83  tff(c_1849, plain, (v4_relat_1('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_1755, c_1845])).
% 4.56/1.83  tff(c_1857, plain, (![B_248, A_249]: (r1_tarski(k1_relat_1(B_248), A_249) | ~v4_relat_1(B_248, A_249) | ~v1_relat_1(B_248))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.56/1.83  tff(c_1879, plain, (![B_253]: (k1_relat_1(B_253)='#skF_1' | ~v4_relat_1(B_253, '#skF_1') | ~v1_relat_1(B_253))), inference(resolution, [status(thm)], [c_1857, c_1761])).
% 4.56/1.83  tff(c_1882, plain, (k1_relat_1('#skF_4')='#skF_1' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_1849, c_1879])).
% 4.56/1.83  tff(c_1885, plain, (k1_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1783, c_1882])).
% 4.56/1.83  tff(c_1813, plain, (k2_relat_1('#skF_4')='#skF_1' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_1809, c_1791])).
% 4.56/1.83  tff(c_1816, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1783, c_1813])).
% 4.56/1.83  tff(c_2005, plain, (![C_269, A_270, B_271]: (m1_subset_1(C_269, k1_zfmisc_1(k2_zfmisc_1(A_270, B_271))) | ~r1_tarski(k2_relat_1(C_269), B_271) | ~r1_tarski(k1_relat_1(C_269), A_270) | ~v1_relat_1(C_269))), inference(cnfTransformation, [status(thm)], [f_76])).
% 4.56/1.83  tff(c_2043, plain, (![A_272, B_273, C_274]: (k1_relset_1(A_272, B_273, C_274)=k1_relat_1(C_274) | ~r1_tarski(k2_relat_1(C_274), B_273) | ~r1_tarski(k1_relat_1(C_274), A_272) | ~v1_relat_1(C_274))), inference(resolution, [status(thm)], [c_2005, c_26])).
% 4.56/1.83  tff(c_2045, plain, (![A_272, B_273]: (k1_relset_1(A_272, B_273, '#skF_4')=k1_relat_1('#skF_4') | ~r1_tarski('#skF_1', B_273) | ~r1_tarski(k1_relat_1('#skF_4'), A_272) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1816, c_2043])).
% 4.56/1.83  tff(c_2052, plain, (![A_272, B_273]: (k1_relset_1(A_272, B_273, '#skF_4')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1783, c_1741, c_1885, c_1741, c_1885, c_2045])).
% 4.56/1.83  tff(c_34, plain, (![C_26, B_25]: (v1_funct_2(C_26, k1_xboole_0, B_25) | k1_relset_1(k1_xboole_0, B_25, C_26)!=k1_xboole_0 | ~m1_subset_1(C_26, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_25))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 4.56/1.83  tff(c_1997, plain, (![C_26, B_25]: (v1_funct_2(C_26, '#skF_1', B_25) | k1_relset_1('#skF_1', B_25, C_26)!='#skF_1' | ~m1_subset_1(C_26, k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_25))))), inference(demodulation, [status(thm), theory('equality')], [c_1739, c_1739, c_1739, c_1739, c_34])).
% 4.56/1.83  tff(c_2340, plain, (![C_308, B_309]: (v1_funct_2(C_308, '#skF_1', B_309) | k1_relset_1('#skF_1', B_309, C_308)!='#skF_1' | ~r1_tarski(k2_relat_1(C_308), B_309) | ~r1_tarski(k1_relat_1(C_308), '#skF_1') | ~v1_relat_1(C_308))), inference(resolution, [status(thm)], [c_2005, c_1997])).
% 4.56/1.83  tff(c_2343, plain, (![B_309]: (v1_funct_2('#skF_4', '#skF_1', B_309) | k1_relset_1('#skF_1', B_309, '#skF_4')!='#skF_1' | ~r1_tarski('#skF_1', B_309) | ~r1_tarski(k1_relat_1('#skF_4'), '#skF_1') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1816, c_2340])).
% 4.56/1.83  tff(c_2352, plain, (![B_309]: (v1_funct_2('#skF_4', '#skF_1', B_309))), inference(demodulation, [status(thm), theory('equality')], [c_1783, c_1741, c_1885, c_1741, c_2052, c_2343])).
% 4.56/1.83  tff(c_1810, plain, (~v1_funct_2('#skF_4', '#skF_1', '#skF_3')), inference(splitLeft, [status(thm)], [c_54])).
% 4.56/1.83  tff(c_2358, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2352, c_1810])).
% 4.56/1.83  tff(c_2359, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3')))), inference(splitRight, [status(thm)], [c_54])).
% 4.56/1.83  tff(c_2580, plain, (~r1_tarski(k2_relat_1('#skF_4'), '#skF_3') | ~r1_tarski(k1_relat_1('#skF_4'), '#skF_1') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_2555, c_2359])).
% 4.56/1.83  tff(c_2596, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1783, c_1741, c_2426, c_1741, c_2366, c_2580])).
% 4.56/1.83  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.56/1.83  
% 4.56/1.83  Inference rules
% 4.56/1.83  ----------------------
% 4.56/1.83  #Ref     : 0
% 4.56/1.83  #Sup     : 467
% 4.56/1.83  #Fact    : 0
% 4.56/1.83  #Define  : 0
% 4.56/1.83  #Split   : 18
% 4.56/1.83  #Chain   : 0
% 4.56/1.83  #Close   : 0
% 4.56/1.83  
% 4.56/1.83  Ordering : KBO
% 4.56/1.83  
% 4.56/1.83  Simplification rules
% 4.56/1.83  ----------------------
% 4.56/1.83  #Subsume      : 94
% 4.56/1.83  #Demod        : 756
% 4.56/1.83  #Tautology    : 218
% 4.56/1.83  #SimpNegUnit  : 7
% 4.56/1.83  #BackRed      : 122
% 4.56/1.83  
% 4.56/1.83  #Partial instantiations: 0
% 4.56/1.83  #Strategies tried      : 1
% 4.56/1.83  
% 4.56/1.83  Timing (in seconds)
% 4.56/1.83  ----------------------
% 4.56/1.84  Preprocessing        : 0.33
% 4.56/1.84  Parsing              : 0.18
% 4.56/1.84  CNF conversion       : 0.02
% 4.56/1.84  Main loop            : 0.66
% 4.56/1.84  Inferencing          : 0.23
% 4.56/1.84  Reduction            : 0.21
% 4.56/1.84  Demodulation         : 0.14
% 4.56/1.84  BG Simplification    : 0.03
% 4.56/1.84  Subsumption          : 0.13
% 4.56/1.84  Abstraction          : 0.03
% 4.56/1.84  MUC search           : 0.00
% 4.56/1.84  Cooper               : 0.00
% 4.56/1.84  Total                : 1.06
% 4.56/1.84  Index Insertion      : 0.00
% 4.56/1.84  Index Deletion       : 0.00
% 4.56/1.84  Index Matching       : 0.00
% 4.56/1.84  BG Taut test         : 0.00
%------------------------------------------------------------------------------
