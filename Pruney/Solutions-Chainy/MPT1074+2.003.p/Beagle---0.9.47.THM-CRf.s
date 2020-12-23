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
% DateTime   : Thu Dec  3 10:18:06 EST 2020

% Result     : Theorem 5.52s
% Output     : CNFRefutation 5.87s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 498 expanded)
%              Number of leaves         :   35 ( 186 expanded)
%              Depth                    :   26
%              Number of atoms          :  220 (1528 expanded)
%              Number of equality atoms :   10 (  40 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k3_funct_2 > k2_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k3_funct_2,type,(
    k3_funct_2: ( $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_114,negated_conjecture,(
    ~ ! [A,B] :
        ( ~ v1_xboole_0(B)
       => ! [C] :
            ( ~ v1_xboole_0(C)
           => ! [D] :
                ( ( v1_funct_1(D)
                  & v1_funct_2(D,B,C)
                  & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
               => ( ! [E] :
                      ( m1_subset_1(E,B)
                     => r2_hidden(k3_funct_2(B,C,D,E),A) )
                 => r1_tarski(k2_relset_1(B,C,D),A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t191_funct_2)).

tff(f_52,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_42,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_58,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_92,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( ( k1_relat_1(C) = A
          & ! [D] :
              ( r2_hidden(D,A)
             => r2_hidden(k1_funct_1(C,D),B) ) )
       => ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_funct_2)).

tff(f_36,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(f_75,axiom,(
    ! [A,B,C,D] :
      ( ( ~ v1_xboole_0(A)
        & v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,A) )
     => k3_funct_2(A,B,C,D) = k1_funct_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

tff(c_44,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_71,plain,(
    ! [C_49,A_50,B_51] :
      ( v1_relat_1(C_49)
      | ~ m1_subset_1(C_49,k1_zfmisc_1(k2_zfmisc_1(A_50,B_51))) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_75,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_44,c_71])).

tff(c_16,plain,(
    ! [B_11,A_10] :
      ( r1_tarski(k2_relat_1(B_11),A_10)
      | ~ v5_relat_1(B_11,A_10)
      | ~ v1_relat_1(B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_163,plain,(
    ! [A_80,B_81,C_82] :
      ( k2_relset_1(A_80,B_81,C_82) = k2_relat_1(C_82)
      | ~ m1_subset_1(C_82,k1_zfmisc_1(k2_zfmisc_1(A_80,B_81))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_177,plain,(
    k2_relset_1('#skF_4','#skF_5','#skF_6') = k2_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_44,c_163])).

tff(c_40,plain,(
    ~ r1_tarski(k2_relset_1('#skF_4','#skF_5','#skF_6'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_178,plain,(
    ~ r1_tarski(k2_relat_1('#skF_6'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_177,c_40])).

tff(c_185,plain,
    ( ~ v5_relat_1('#skF_6','#skF_3')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_16,c_178])).

tff(c_188,plain,(
    ~ v5_relat_1('#skF_6','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_185])).

tff(c_48,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_55,plain,(
    ! [A_45,B_46] :
      ( r2_hidden('#skF_1'(A_45,B_46),A_45)
      | r1_tarski(A_45,B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_63,plain,(
    ! [A_45] : r1_tarski(A_45,A_45) ),
    inference(resolution,[status(thm)],[c_55,c_4])).

tff(c_122,plain,(
    ! [B_69,A_70] :
      ( v4_relat_1(B_69,A_70)
      | ~ r1_tarski(k1_relat_1(B_69),A_70)
      | ~ v1_relat_1(B_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_127,plain,(
    ! [B_69] :
      ( v4_relat_1(B_69,k1_relat_1(B_69))
      | ~ v1_relat_1(B_69) ) ),
    inference(resolution,[status(thm)],[c_63,c_122])).

tff(c_93,plain,(
    ! [C_59,A_60,B_61] :
      ( v4_relat_1(C_59,A_60)
      | ~ m1_subset_1(C_59,k1_zfmisc_1(k2_zfmisc_1(A_60,B_61))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_102,plain,(
    v4_relat_1('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_93])).

tff(c_12,plain,(
    ! [B_9,A_8] :
      ( r1_tarski(k1_relat_1(B_9),A_8)
      | ~ v4_relat_1(B_9,A_8)
      | ~ v1_relat_1(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_115,plain,(
    ! [C_66,B_67,A_68] :
      ( r2_hidden(C_66,B_67)
      | ~ r2_hidden(C_66,A_68)
      | ~ r1_tarski(A_68,B_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_134,plain,(
    ! [A_74,B_75,B_76] :
      ( r2_hidden('#skF_1'(A_74,B_75),B_76)
      | ~ r1_tarski(A_74,B_76)
      | r1_tarski(A_74,B_75) ) ),
    inference(resolution,[status(thm)],[c_6,c_115])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_240,plain,(
    ! [A_96,B_97,B_98,B_99] :
      ( r2_hidden('#skF_1'(A_96,B_97),B_98)
      | ~ r1_tarski(B_99,B_98)
      | ~ r1_tarski(A_96,B_99)
      | r1_tarski(A_96,B_97) ) ),
    inference(resolution,[status(thm)],[c_134,c_2])).

tff(c_340,plain,(
    ! [A_136,B_137,A_138,B_139] :
      ( r2_hidden('#skF_1'(A_136,B_137),A_138)
      | ~ r1_tarski(A_136,k1_relat_1(B_139))
      | r1_tarski(A_136,B_137)
      | ~ v4_relat_1(B_139,A_138)
      | ~ v1_relat_1(B_139) ) ),
    inference(resolution,[status(thm)],[c_12,c_240])).

tff(c_1380,plain,(
    ! [B_343,B_344,A_345,B_346] :
      ( r2_hidden('#skF_1'(k1_relat_1(B_343),B_344),A_345)
      | r1_tarski(k1_relat_1(B_343),B_344)
      | ~ v4_relat_1(B_346,A_345)
      | ~ v1_relat_1(B_346)
      | ~ v4_relat_1(B_343,k1_relat_1(B_346))
      | ~ v1_relat_1(B_343) ) ),
    inference(resolution,[status(thm)],[c_12,c_340])).

tff(c_1386,plain,(
    ! [B_343,B_344] :
      ( r2_hidden('#skF_1'(k1_relat_1(B_343),B_344),'#skF_4')
      | r1_tarski(k1_relat_1(B_343),B_344)
      | ~ v1_relat_1('#skF_6')
      | ~ v4_relat_1(B_343,k1_relat_1('#skF_6'))
      | ~ v1_relat_1(B_343) ) ),
    inference(resolution,[status(thm)],[c_102,c_1380])).

tff(c_1392,plain,(
    ! [B_347,B_348] :
      ( r2_hidden('#skF_1'(k1_relat_1(B_347),B_348),'#skF_4')
      | r1_tarski(k1_relat_1(B_347),B_348)
      | ~ v4_relat_1(B_347,k1_relat_1('#skF_6'))
      | ~ v1_relat_1(B_347) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_1386])).

tff(c_1462,plain,(
    ! [B_353] :
      ( r1_tarski(k1_relat_1(B_353),'#skF_4')
      | ~ v4_relat_1(B_353,k1_relat_1('#skF_6'))
      | ~ v1_relat_1(B_353) ) ),
    inference(resolution,[status(thm)],[c_1392,c_4])).

tff(c_1470,plain,
    ( r1_tarski(k1_relat_1('#skF_6'),'#skF_4')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_127,c_1462])).

tff(c_1474,plain,(
    r1_tarski(k1_relat_1('#skF_6'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_1470])).

tff(c_366,plain,(
    ! [C_143,B_144] :
      ( r2_hidden('#skF_2'(k1_relat_1(C_143),B_144,C_143),k1_relat_1(C_143))
      | m1_subset_1(C_143,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(C_143),B_144)))
      | ~ v1_funct_1(C_143)
      | ~ v1_relat_1(C_143) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_578,plain,(
    ! [C_208,B_209,B_210] :
      ( r2_hidden('#skF_2'(k1_relat_1(C_208),B_209,C_208),B_210)
      | ~ r1_tarski(k1_relat_1(C_208),B_210)
      | m1_subset_1(C_208,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(C_208),B_209)))
      | ~ v1_funct_1(C_208)
      | ~ v1_relat_1(C_208) ) ),
    inference(resolution,[status(thm)],[c_366,c_2])).

tff(c_20,plain,(
    ! [C_17,B_16,A_15] :
      ( v5_relat_1(C_17,B_16)
      | ~ m1_subset_1(C_17,k1_zfmisc_1(k2_zfmisc_1(A_15,B_16))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_662,plain,(
    ! [C_218,B_219,B_220] :
      ( v5_relat_1(C_218,B_219)
      | r2_hidden('#skF_2'(k1_relat_1(C_218),B_219,C_218),B_220)
      | ~ r1_tarski(k1_relat_1(C_218),B_220)
      | ~ v1_funct_1(C_218)
      | ~ v1_relat_1(C_218) ) ),
    inference(resolution,[status(thm)],[c_578,c_20])).

tff(c_668,plain,(
    ! [C_218,B_219,B_2,B_220] :
      ( r2_hidden('#skF_2'(k1_relat_1(C_218),B_219,C_218),B_2)
      | ~ r1_tarski(B_220,B_2)
      | v5_relat_1(C_218,B_219)
      | ~ r1_tarski(k1_relat_1(C_218),B_220)
      | ~ v1_funct_1(C_218)
      | ~ v1_relat_1(C_218) ) ),
    inference(resolution,[status(thm)],[c_662,c_2])).

tff(c_2553,plain,(
    ! [C_434,B_435] :
      ( r2_hidden('#skF_2'(k1_relat_1(C_434),B_435,C_434),'#skF_4')
      | v5_relat_1(C_434,B_435)
      | ~ r1_tarski(k1_relat_1(C_434),k1_relat_1('#skF_6'))
      | ~ v1_funct_1(C_434)
      | ~ v1_relat_1(C_434) ) ),
    inference(resolution,[status(thm)],[c_1474,c_668])).

tff(c_8,plain,(
    ! [A_6,B_7] :
      ( m1_subset_1(A_6,B_7)
      | ~ r2_hidden(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_2596,plain,(
    ! [C_445,B_446] :
      ( m1_subset_1('#skF_2'(k1_relat_1(C_445),B_446,C_445),'#skF_4')
      | v5_relat_1(C_445,B_446)
      | ~ r1_tarski(k1_relat_1(C_445),k1_relat_1('#skF_6'))
      | ~ v1_funct_1(C_445)
      | ~ v1_relat_1(C_445) ) ),
    inference(resolution,[status(thm)],[c_2553,c_8])).

tff(c_2605,plain,(
    ! [B_446] :
      ( m1_subset_1('#skF_2'(k1_relat_1('#skF_6'),B_446,'#skF_6'),'#skF_4')
      | v5_relat_1('#skF_6',B_446)
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_63,c_2596])).

tff(c_2612,plain,(
    ! [B_446] :
      ( m1_subset_1('#skF_2'(k1_relat_1('#skF_6'),B_446,'#skF_6'),'#skF_4')
      | v5_relat_1('#skF_6',B_446) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_48,c_2605])).

tff(c_46,plain,(
    v1_funct_2('#skF_6','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_52,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_2621,plain,(
    ! [B_449] :
      ( m1_subset_1('#skF_2'(k1_relat_1('#skF_6'),B_449,'#skF_6'),'#skF_4')
      | v5_relat_1('#skF_6',B_449) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_48,c_2605])).

tff(c_26,plain,(
    ! [A_21,B_22,C_23,D_24] :
      ( k3_funct_2(A_21,B_22,C_23,D_24) = k1_funct_1(C_23,D_24)
      | ~ m1_subset_1(D_24,A_21)
      | ~ m1_subset_1(C_23,k1_zfmisc_1(k2_zfmisc_1(A_21,B_22)))
      | ~ v1_funct_2(C_23,A_21,B_22)
      | ~ v1_funct_1(C_23)
      | v1_xboole_0(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_2623,plain,(
    ! [B_22,C_23,B_449] :
      ( k3_funct_2('#skF_4',B_22,C_23,'#skF_2'(k1_relat_1('#skF_6'),B_449,'#skF_6')) = k1_funct_1(C_23,'#skF_2'(k1_relat_1('#skF_6'),B_449,'#skF_6'))
      | ~ m1_subset_1(C_23,k1_zfmisc_1(k2_zfmisc_1('#skF_4',B_22)))
      | ~ v1_funct_2(C_23,'#skF_4',B_22)
      | ~ v1_funct_1(C_23)
      | v1_xboole_0('#skF_4')
      | v5_relat_1('#skF_6',B_449) ) ),
    inference(resolution,[status(thm)],[c_2621,c_26])).

tff(c_2681,plain,(
    ! [B_460,C_461,B_462] :
      ( k3_funct_2('#skF_4',B_460,C_461,'#skF_2'(k1_relat_1('#skF_6'),B_462,'#skF_6')) = k1_funct_1(C_461,'#skF_2'(k1_relat_1('#skF_6'),B_462,'#skF_6'))
      | ~ m1_subset_1(C_461,k1_zfmisc_1(k2_zfmisc_1('#skF_4',B_460)))
      | ~ v1_funct_2(C_461,'#skF_4',B_460)
      | ~ v1_funct_1(C_461)
      | v5_relat_1('#skF_6',B_462) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_2623])).

tff(c_2728,plain,(
    ! [B_462] :
      ( k3_funct_2('#skF_4','#skF_5','#skF_6','#skF_2'(k1_relat_1('#skF_6'),B_462,'#skF_6')) = k1_funct_1('#skF_6','#skF_2'(k1_relat_1('#skF_6'),B_462,'#skF_6'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_5')
      | ~ v1_funct_1('#skF_6')
      | v5_relat_1('#skF_6',B_462) ) ),
    inference(resolution,[status(thm)],[c_44,c_2681])).

tff(c_2843,plain,(
    ! [B_472] :
      ( k3_funct_2('#skF_4','#skF_5','#skF_6','#skF_2'(k1_relat_1('#skF_6'),B_472,'#skF_6')) = k1_funct_1('#skF_6','#skF_2'(k1_relat_1('#skF_6'),B_472,'#skF_6'))
      | v5_relat_1('#skF_6',B_472) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_2728])).

tff(c_42,plain,(
    ! [E_40] :
      ( r2_hidden(k3_funct_2('#skF_4','#skF_5','#skF_6',E_40),'#skF_3')
      | ~ m1_subset_1(E_40,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_2869,plain,(
    ! [B_474] :
      ( r2_hidden(k1_funct_1('#skF_6','#skF_2'(k1_relat_1('#skF_6'),B_474,'#skF_6')),'#skF_3')
      | ~ m1_subset_1('#skF_2'(k1_relat_1('#skF_6'),B_474,'#skF_6'),'#skF_4')
      | v5_relat_1('#skF_6',B_474) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2843,c_42])).

tff(c_32,plain,(
    ! [C_27,B_26] :
      ( ~ r2_hidden(k1_funct_1(C_27,'#skF_2'(k1_relat_1(C_27),B_26,C_27)),B_26)
      | v1_funct_2(C_27,k1_relat_1(C_27),B_26)
      | ~ v1_funct_1(C_27)
      | ~ v1_relat_1(C_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_2877,plain,
    ( v1_funct_2('#skF_6',k1_relat_1('#skF_6'),'#skF_3')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6')
    | ~ m1_subset_1('#skF_2'(k1_relat_1('#skF_6'),'#skF_3','#skF_6'),'#skF_4')
    | v5_relat_1('#skF_6','#skF_3') ),
    inference(resolution,[status(thm)],[c_2869,c_32])).

tff(c_2889,plain,
    ( v1_funct_2('#skF_6',k1_relat_1('#skF_6'),'#skF_3')
    | ~ m1_subset_1('#skF_2'(k1_relat_1('#skF_6'),'#skF_3','#skF_6'),'#skF_4')
    | v5_relat_1('#skF_6','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_48,c_2877])).

tff(c_2890,plain,
    ( v1_funct_2('#skF_6',k1_relat_1('#skF_6'),'#skF_3')
    | ~ m1_subset_1('#skF_2'(k1_relat_1('#skF_6'),'#skF_3','#skF_6'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_188,c_2889])).

tff(c_2893,plain,(
    ~ m1_subset_1('#skF_2'(k1_relat_1('#skF_6'),'#skF_3','#skF_6'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_2890])).

tff(c_2899,plain,(
    v5_relat_1('#skF_6','#skF_3') ),
    inference(resolution,[status(thm)],[c_2612,c_2893])).

tff(c_2917,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_188,c_2899])).

tff(c_2919,plain,(
    m1_subset_1('#skF_2'(k1_relat_1('#skF_6'),'#skF_3','#skF_6'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_2890])).

tff(c_28,plain,(
    ! [C_27,B_26] :
      ( ~ r2_hidden(k1_funct_1(C_27,'#skF_2'(k1_relat_1(C_27),B_26,C_27)),B_26)
      | m1_subset_1(C_27,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(C_27),B_26)))
      | ~ v1_funct_1(C_27)
      | ~ v1_relat_1(C_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_2873,plain,
    ( m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_6'),'#skF_3')))
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6')
    | ~ m1_subset_1('#skF_2'(k1_relat_1('#skF_6'),'#skF_3','#skF_6'),'#skF_4')
    | v5_relat_1('#skF_6','#skF_3') ),
    inference(resolution,[status(thm)],[c_2869,c_28])).

tff(c_2885,plain,
    ( m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_6'),'#skF_3')))
    | ~ m1_subset_1('#skF_2'(k1_relat_1('#skF_6'),'#skF_3','#skF_6'),'#skF_4')
    | v5_relat_1('#skF_6','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_48,c_2873])).

tff(c_2886,plain,
    ( m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_6'),'#skF_3')))
    | ~ m1_subset_1('#skF_2'(k1_relat_1('#skF_6'),'#skF_3','#skF_6'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_188,c_2885])).

tff(c_2926,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_6'),'#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2919,c_2886])).

tff(c_2943,plain,(
    v5_relat_1('#skF_6','#skF_3') ),
    inference(resolution,[status(thm)],[c_2926,c_20])).

tff(c_2962,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_188,c_2943])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:52:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.52/2.07  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.52/2.08  
% 5.52/2.08  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.52/2.08  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k3_funct_2 > k2_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4 > #skF_1
% 5.52/2.08  
% 5.52/2.08  %Foreground sorts:
% 5.52/2.08  
% 5.52/2.08  
% 5.52/2.08  %Background operators:
% 5.52/2.08  
% 5.52/2.08  
% 5.52/2.08  %Foreground operators:
% 5.52/2.08  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 5.52/2.08  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.52/2.08  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.52/2.08  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.52/2.08  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.52/2.08  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.52/2.08  tff('#skF_5', type, '#skF_5': $i).
% 5.52/2.08  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.52/2.08  tff('#skF_6', type, '#skF_6': $i).
% 5.52/2.08  tff('#skF_3', type, '#skF_3': $i).
% 5.52/2.08  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 5.52/2.08  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 5.52/2.08  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.52/2.08  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 5.52/2.08  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.52/2.08  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.52/2.08  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.52/2.08  tff('#skF_4', type, '#skF_4': $i).
% 5.52/2.08  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.52/2.08  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 5.52/2.08  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.52/2.08  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.52/2.08  tff(k3_funct_2, type, k3_funct_2: ($i * $i * $i * $i) > $i).
% 5.52/2.08  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.52/2.08  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.52/2.08  
% 5.87/2.10  tff(f_114, negated_conjecture, ~(![A, B]: (~v1_xboole_0(B) => (![C]: (~v1_xboole_0(C) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => ((![E]: (m1_subset_1(E, B) => r2_hidden(k3_funct_2(B, C, D, E), A))) => r1_tarski(k2_relset_1(B, C, D), A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t191_funct_2)).
% 5.87/2.10  tff(f_52, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 5.87/2.10  tff(f_48, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 5.87/2.10  tff(f_62, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 5.87/2.10  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 5.87/2.10  tff(f_42, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 5.87/2.10  tff(f_58, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 5.87/2.10  tff(f_92, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (((k1_relat_1(C) = A) & (![D]: (r2_hidden(D, A) => r2_hidden(k1_funct_1(C, D), B)))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_funct_2)).
% 5.87/2.10  tff(f_36, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 5.87/2.10  tff(f_75, axiom, (![A, B, C, D]: (((((~v1_xboole_0(A) & v1_funct_1(C)) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & m1_subset_1(D, A)) => (k3_funct_2(A, B, C, D) = k1_funct_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k3_funct_2)).
% 5.87/2.10  tff(c_44, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_114])).
% 5.87/2.10  tff(c_71, plain, (![C_49, A_50, B_51]: (v1_relat_1(C_49) | ~m1_subset_1(C_49, k1_zfmisc_1(k2_zfmisc_1(A_50, B_51))))), inference(cnfTransformation, [status(thm)], [f_52])).
% 5.87/2.10  tff(c_75, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_44, c_71])).
% 5.87/2.10  tff(c_16, plain, (![B_11, A_10]: (r1_tarski(k2_relat_1(B_11), A_10) | ~v5_relat_1(B_11, A_10) | ~v1_relat_1(B_11))), inference(cnfTransformation, [status(thm)], [f_48])).
% 5.87/2.10  tff(c_163, plain, (![A_80, B_81, C_82]: (k2_relset_1(A_80, B_81, C_82)=k2_relat_1(C_82) | ~m1_subset_1(C_82, k1_zfmisc_1(k2_zfmisc_1(A_80, B_81))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 5.87/2.10  tff(c_177, plain, (k2_relset_1('#skF_4', '#skF_5', '#skF_6')=k2_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_44, c_163])).
% 5.87/2.10  tff(c_40, plain, (~r1_tarski(k2_relset_1('#skF_4', '#skF_5', '#skF_6'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_114])).
% 5.87/2.10  tff(c_178, plain, (~r1_tarski(k2_relat_1('#skF_6'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_177, c_40])).
% 5.87/2.10  tff(c_185, plain, (~v5_relat_1('#skF_6', '#skF_3') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_16, c_178])).
% 5.87/2.10  tff(c_188, plain, (~v5_relat_1('#skF_6', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_75, c_185])).
% 5.87/2.10  tff(c_48, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_114])).
% 5.87/2.10  tff(c_55, plain, (![A_45, B_46]: (r2_hidden('#skF_1'(A_45, B_46), A_45) | r1_tarski(A_45, B_46))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.87/2.10  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.87/2.10  tff(c_63, plain, (![A_45]: (r1_tarski(A_45, A_45))), inference(resolution, [status(thm)], [c_55, c_4])).
% 5.87/2.10  tff(c_122, plain, (![B_69, A_70]: (v4_relat_1(B_69, A_70) | ~r1_tarski(k1_relat_1(B_69), A_70) | ~v1_relat_1(B_69))), inference(cnfTransformation, [status(thm)], [f_42])).
% 5.87/2.10  tff(c_127, plain, (![B_69]: (v4_relat_1(B_69, k1_relat_1(B_69)) | ~v1_relat_1(B_69))), inference(resolution, [status(thm)], [c_63, c_122])).
% 5.87/2.10  tff(c_93, plain, (![C_59, A_60, B_61]: (v4_relat_1(C_59, A_60) | ~m1_subset_1(C_59, k1_zfmisc_1(k2_zfmisc_1(A_60, B_61))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 5.87/2.10  tff(c_102, plain, (v4_relat_1('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_44, c_93])).
% 5.87/2.10  tff(c_12, plain, (![B_9, A_8]: (r1_tarski(k1_relat_1(B_9), A_8) | ~v4_relat_1(B_9, A_8) | ~v1_relat_1(B_9))), inference(cnfTransformation, [status(thm)], [f_42])).
% 5.87/2.10  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.87/2.10  tff(c_115, plain, (![C_66, B_67, A_68]: (r2_hidden(C_66, B_67) | ~r2_hidden(C_66, A_68) | ~r1_tarski(A_68, B_67))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.87/2.10  tff(c_134, plain, (![A_74, B_75, B_76]: (r2_hidden('#skF_1'(A_74, B_75), B_76) | ~r1_tarski(A_74, B_76) | r1_tarski(A_74, B_75))), inference(resolution, [status(thm)], [c_6, c_115])).
% 5.87/2.10  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.87/2.10  tff(c_240, plain, (![A_96, B_97, B_98, B_99]: (r2_hidden('#skF_1'(A_96, B_97), B_98) | ~r1_tarski(B_99, B_98) | ~r1_tarski(A_96, B_99) | r1_tarski(A_96, B_97))), inference(resolution, [status(thm)], [c_134, c_2])).
% 5.87/2.10  tff(c_340, plain, (![A_136, B_137, A_138, B_139]: (r2_hidden('#skF_1'(A_136, B_137), A_138) | ~r1_tarski(A_136, k1_relat_1(B_139)) | r1_tarski(A_136, B_137) | ~v4_relat_1(B_139, A_138) | ~v1_relat_1(B_139))), inference(resolution, [status(thm)], [c_12, c_240])).
% 5.87/2.10  tff(c_1380, plain, (![B_343, B_344, A_345, B_346]: (r2_hidden('#skF_1'(k1_relat_1(B_343), B_344), A_345) | r1_tarski(k1_relat_1(B_343), B_344) | ~v4_relat_1(B_346, A_345) | ~v1_relat_1(B_346) | ~v4_relat_1(B_343, k1_relat_1(B_346)) | ~v1_relat_1(B_343))), inference(resolution, [status(thm)], [c_12, c_340])).
% 5.87/2.10  tff(c_1386, plain, (![B_343, B_344]: (r2_hidden('#skF_1'(k1_relat_1(B_343), B_344), '#skF_4') | r1_tarski(k1_relat_1(B_343), B_344) | ~v1_relat_1('#skF_6') | ~v4_relat_1(B_343, k1_relat_1('#skF_6')) | ~v1_relat_1(B_343))), inference(resolution, [status(thm)], [c_102, c_1380])).
% 5.87/2.10  tff(c_1392, plain, (![B_347, B_348]: (r2_hidden('#skF_1'(k1_relat_1(B_347), B_348), '#skF_4') | r1_tarski(k1_relat_1(B_347), B_348) | ~v4_relat_1(B_347, k1_relat_1('#skF_6')) | ~v1_relat_1(B_347))), inference(demodulation, [status(thm), theory('equality')], [c_75, c_1386])).
% 5.87/2.10  tff(c_1462, plain, (![B_353]: (r1_tarski(k1_relat_1(B_353), '#skF_4') | ~v4_relat_1(B_353, k1_relat_1('#skF_6')) | ~v1_relat_1(B_353))), inference(resolution, [status(thm)], [c_1392, c_4])).
% 5.87/2.10  tff(c_1470, plain, (r1_tarski(k1_relat_1('#skF_6'), '#skF_4') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_127, c_1462])).
% 5.87/2.10  tff(c_1474, plain, (r1_tarski(k1_relat_1('#skF_6'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_75, c_1470])).
% 5.87/2.10  tff(c_366, plain, (![C_143, B_144]: (r2_hidden('#skF_2'(k1_relat_1(C_143), B_144, C_143), k1_relat_1(C_143)) | m1_subset_1(C_143, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(C_143), B_144))) | ~v1_funct_1(C_143) | ~v1_relat_1(C_143))), inference(cnfTransformation, [status(thm)], [f_92])).
% 5.87/2.10  tff(c_578, plain, (![C_208, B_209, B_210]: (r2_hidden('#skF_2'(k1_relat_1(C_208), B_209, C_208), B_210) | ~r1_tarski(k1_relat_1(C_208), B_210) | m1_subset_1(C_208, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(C_208), B_209))) | ~v1_funct_1(C_208) | ~v1_relat_1(C_208))), inference(resolution, [status(thm)], [c_366, c_2])).
% 5.87/2.10  tff(c_20, plain, (![C_17, B_16, A_15]: (v5_relat_1(C_17, B_16) | ~m1_subset_1(C_17, k1_zfmisc_1(k2_zfmisc_1(A_15, B_16))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 5.87/2.10  tff(c_662, plain, (![C_218, B_219, B_220]: (v5_relat_1(C_218, B_219) | r2_hidden('#skF_2'(k1_relat_1(C_218), B_219, C_218), B_220) | ~r1_tarski(k1_relat_1(C_218), B_220) | ~v1_funct_1(C_218) | ~v1_relat_1(C_218))), inference(resolution, [status(thm)], [c_578, c_20])).
% 5.87/2.10  tff(c_668, plain, (![C_218, B_219, B_2, B_220]: (r2_hidden('#skF_2'(k1_relat_1(C_218), B_219, C_218), B_2) | ~r1_tarski(B_220, B_2) | v5_relat_1(C_218, B_219) | ~r1_tarski(k1_relat_1(C_218), B_220) | ~v1_funct_1(C_218) | ~v1_relat_1(C_218))), inference(resolution, [status(thm)], [c_662, c_2])).
% 5.87/2.10  tff(c_2553, plain, (![C_434, B_435]: (r2_hidden('#skF_2'(k1_relat_1(C_434), B_435, C_434), '#skF_4') | v5_relat_1(C_434, B_435) | ~r1_tarski(k1_relat_1(C_434), k1_relat_1('#skF_6')) | ~v1_funct_1(C_434) | ~v1_relat_1(C_434))), inference(resolution, [status(thm)], [c_1474, c_668])).
% 5.87/2.10  tff(c_8, plain, (![A_6, B_7]: (m1_subset_1(A_6, B_7) | ~r2_hidden(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_36])).
% 5.87/2.10  tff(c_2596, plain, (![C_445, B_446]: (m1_subset_1('#skF_2'(k1_relat_1(C_445), B_446, C_445), '#skF_4') | v5_relat_1(C_445, B_446) | ~r1_tarski(k1_relat_1(C_445), k1_relat_1('#skF_6')) | ~v1_funct_1(C_445) | ~v1_relat_1(C_445))), inference(resolution, [status(thm)], [c_2553, c_8])).
% 5.87/2.10  tff(c_2605, plain, (![B_446]: (m1_subset_1('#skF_2'(k1_relat_1('#skF_6'), B_446, '#skF_6'), '#skF_4') | v5_relat_1('#skF_6', B_446) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_63, c_2596])).
% 5.87/2.10  tff(c_2612, plain, (![B_446]: (m1_subset_1('#skF_2'(k1_relat_1('#skF_6'), B_446, '#skF_6'), '#skF_4') | v5_relat_1('#skF_6', B_446))), inference(demodulation, [status(thm), theory('equality')], [c_75, c_48, c_2605])).
% 5.87/2.10  tff(c_46, plain, (v1_funct_2('#skF_6', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_114])).
% 5.87/2.10  tff(c_52, plain, (~v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_114])).
% 5.87/2.10  tff(c_2621, plain, (![B_449]: (m1_subset_1('#skF_2'(k1_relat_1('#skF_6'), B_449, '#skF_6'), '#skF_4') | v5_relat_1('#skF_6', B_449))), inference(demodulation, [status(thm), theory('equality')], [c_75, c_48, c_2605])).
% 5.87/2.10  tff(c_26, plain, (![A_21, B_22, C_23, D_24]: (k3_funct_2(A_21, B_22, C_23, D_24)=k1_funct_1(C_23, D_24) | ~m1_subset_1(D_24, A_21) | ~m1_subset_1(C_23, k1_zfmisc_1(k2_zfmisc_1(A_21, B_22))) | ~v1_funct_2(C_23, A_21, B_22) | ~v1_funct_1(C_23) | v1_xboole_0(A_21))), inference(cnfTransformation, [status(thm)], [f_75])).
% 5.87/2.10  tff(c_2623, plain, (![B_22, C_23, B_449]: (k3_funct_2('#skF_4', B_22, C_23, '#skF_2'(k1_relat_1('#skF_6'), B_449, '#skF_6'))=k1_funct_1(C_23, '#skF_2'(k1_relat_1('#skF_6'), B_449, '#skF_6')) | ~m1_subset_1(C_23, k1_zfmisc_1(k2_zfmisc_1('#skF_4', B_22))) | ~v1_funct_2(C_23, '#skF_4', B_22) | ~v1_funct_1(C_23) | v1_xboole_0('#skF_4') | v5_relat_1('#skF_6', B_449))), inference(resolution, [status(thm)], [c_2621, c_26])).
% 5.87/2.10  tff(c_2681, plain, (![B_460, C_461, B_462]: (k3_funct_2('#skF_4', B_460, C_461, '#skF_2'(k1_relat_1('#skF_6'), B_462, '#skF_6'))=k1_funct_1(C_461, '#skF_2'(k1_relat_1('#skF_6'), B_462, '#skF_6')) | ~m1_subset_1(C_461, k1_zfmisc_1(k2_zfmisc_1('#skF_4', B_460))) | ~v1_funct_2(C_461, '#skF_4', B_460) | ~v1_funct_1(C_461) | v5_relat_1('#skF_6', B_462))), inference(negUnitSimplification, [status(thm)], [c_52, c_2623])).
% 5.87/2.10  tff(c_2728, plain, (![B_462]: (k3_funct_2('#skF_4', '#skF_5', '#skF_6', '#skF_2'(k1_relat_1('#skF_6'), B_462, '#skF_6'))=k1_funct_1('#skF_6', '#skF_2'(k1_relat_1('#skF_6'), B_462, '#skF_6')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5') | ~v1_funct_1('#skF_6') | v5_relat_1('#skF_6', B_462))), inference(resolution, [status(thm)], [c_44, c_2681])).
% 5.87/2.10  tff(c_2843, plain, (![B_472]: (k3_funct_2('#skF_4', '#skF_5', '#skF_6', '#skF_2'(k1_relat_1('#skF_6'), B_472, '#skF_6'))=k1_funct_1('#skF_6', '#skF_2'(k1_relat_1('#skF_6'), B_472, '#skF_6')) | v5_relat_1('#skF_6', B_472))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_2728])).
% 5.87/2.10  tff(c_42, plain, (![E_40]: (r2_hidden(k3_funct_2('#skF_4', '#skF_5', '#skF_6', E_40), '#skF_3') | ~m1_subset_1(E_40, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_114])).
% 5.87/2.10  tff(c_2869, plain, (![B_474]: (r2_hidden(k1_funct_1('#skF_6', '#skF_2'(k1_relat_1('#skF_6'), B_474, '#skF_6')), '#skF_3') | ~m1_subset_1('#skF_2'(k1_relat_1('#skF_6'), B_474, '#skF_6'), '#skF_4') | v5_relat_1('#skF_6', B_474))), inference(superposition, [status(thm), theory('equality')], [c_2843, c_42])).
% 5.87/2.10  tff(c_32, plain, (![C_27, B_26]: (~r2_hidden(k1_funct_1(C_27, '#skF_2'(k1_relat_1(C_27), B_26, C_27)), B_26) | v1_funct_2(C_27, k1_relat_1(C_27), B_26) | ~v1_funct_1(C_27) | ~v1_relat_1(C_27))), inference(cnfTransformation, [status(thm)], [f_92])).
% 5.87/2.10  tff(c_2877, plain, (v1_funct_2('#skF_6', k1_relat_1('#skF_6'), '#skF_3') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6') | ~m1_subset_1('#skF_2'(k1_relat_1('#skF_6'), '#skF_3', '#skF_6'), '#skF_4') | v5_relat_1('#skF_6', '#skF_3')), inference(resolution, [status(thm)], [c_2869, c_32])).
% 5.87/2.10  tff(c_2889, plain, (v1_funct_2('#skF_6', k1_relat_1('#skF_6'), '#skF_3') | ~m1_subset_1('#skF_2'(k1_relat_1('#skF_6'), '#skF_3', '#skF_6'), '#skF_4') | v5_relat_1('#skF_6', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_75, c_48, c_2877])).
% 5.87/2.10  tff(c_2890, plain, (v1_funct_2('#skF_6', k1_relat_1('#skF_6'), '#skF_3') | ~m1_subset_1('#skF_2'(k1_relat_1('#skF_6'), '#skF_3', '#skF_6'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_188, c_2889])).
% 5.87/2.10  tff(c_2893, plain, (~m1_subset_1('#skF_2'(k1_relat_1('#skF_6'), '#skF_3', '#skF_6'), '#skF_4')), inference(splitLeft, [status(thm)], [c_2890])).
% 5.87/2.10  tff(c_2899, plain, (v5_relat_1('#skF_6', '#skF_3')), inference(resolution, [status(thm)], [c_2612, c_2893])).
% 5.87/2.10  tff(c_2917, plain, $false, inference(negUnitSimplification, [status(thm)], [c_188, c_2899])).
% 5.87/2.10  tff(c_2919, plain, (m1_subset_1('#skF_2'(k1_relat_1('#skF_6'), '#skF_3', '#skF_6'), '#skF_4')), inference(splitRight, [status(thm)], [c_2890])).
% 5.87/2.10  tff(c_28, plain, (![C_27, B_26]: (~r2_hidden(k1_funct_1(C_27, '#skF_2'(k1_relat_1(C_27), B_26, C_27)), B_26) | m1_subset_1(C_27, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(C_27), B_26))) | ~v1_funct_1(C_27) | ~v1_relat_1(C_27))), inference(cnfTransformation, [status(thm)], [f_92])).
% 5.87/2.10  tff(c_2873, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_6'), '#skF_3'))) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6') | ~m1_subset_1('#skF_2'(k1_relat_1('#skF_6'), '#skF_3', '#skF_6'), '#skF_4') | v5_relat_1('#skF_6', '#skF_3')), inference(resolution, [status(thm)], [c_2869, c_28])).
% 5.87/2.10  tff(c_2885, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_6'), '#skF_3'))) | ~m1_subset_1('#skF_2'(k1_relat_1('#skF_6'), '#skF_3', '#skF_6'), '#skF_4') | v5_relat_1('#skF_6', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_75, c_48, c_2873])).
% 5.87/2.10  tff(c_2886, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_6'), '#skF_3'))) | ~m1_subset_1('#skF_2'(k1_relat_1('#skF_6'), '#skF_3', '#skF_6'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_188, c_2885])).
% 5.87/2.10  tff(c_2926, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_6'), '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_2919, c_2886])).
% 5.87/2.10  tff(c_2943, plain, (v5_relat_1('#skF_6', '#skF_3')), inference(resolution, [status(thm)], [c_2926, c_20])).
% 5.87/2.10  tff(c_2962, plain, $false, inference(negUnitSimplification, [status(thm)], [c_188, c_2943])).
% 5.87/2.10  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.87/2.10  
% 5.87/2.10  Inference rules
% 5.87/2.10  ----------------------
% 5.87/2.10  #Ref     : 0
% 5.87/2.10  #Sup     : 664
% 5.87/2.10  #Fact    : 0
% 5.87/2.10  #Define  : 0
% 5.87/2.10  #Split   : 12
% 5.87/2.10  #Chain   : 0
% 5.87/2.10  #Close   : 0
% 5.87/2.10  
% 5.87/2.10  Ordering : KBO
% 5.87/2.10  
% 5.87/2.10  Simplification rules
% 5.87/2.10  ----------------------
% 5.87/2.10  #Subsume      : 240
% 5.87/2.10  #Demod        : 96
% 5.87/2.10  #Tautology    : 34
% 5.87/2.10  #SimpNegUnit  : 16
% 5.87/2.10  #BackRed      : 1
% 5.87/2.10  
% 5.87/2.10  #Partial instantiations: 0
% 5.87/2.10  #Strategies tried      : 1
% 5.87/2.10  
% 5.87/2.10  Timing (in seconds)
% 5.87/2.10  ----------------------
% 5.87/2.10  Preprocessing        : 0.33
% 5.87/2.10  Parsing              : 0.17
% 5.87/2.10  CNF conversion       : 0.02
% 5.87/2.10  Main loop            : 1.00
% 5.87/2.10  Inferencing          : 0.37
% 5.87/2.10  Reduction            : 0.27
% 5.87/2.10  Demodulation         : 0.17
% 5.87/2.10  BG Simplification    : 0.04
% 5.87/2.10  Subsumption          : 0.24
% 5.87/2.10  Abstraction          : 0.06
% 5.87/2.10  MUC search           : 0.00
% 5.87/2.10  Cooper               : 0.00
% 5.87/2.11  Total                : 1.37
% 5.87/2.11  Index Insertion      : 0.00
% 5.87/2.11  Index Deletion       : 0.00
% 5.87/2.11  Index Matching       : 0.00
% 5.87/2.11  BG Taut test         : 0.00
%------------------------------------------------------------------------------
