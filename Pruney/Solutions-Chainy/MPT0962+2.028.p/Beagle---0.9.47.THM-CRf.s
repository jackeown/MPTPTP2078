%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:55 EST 2020

% Result     : Theorem 3.96s
% Output     : CNFRefutation 4.49s
% Verified   : 
% Statistics : Number of formulae       :  133 ( 987 expanded)
%              Number of leaves         :   30 ( 321 expanded)
%              Depth                    :   15
%              Number of atoms          :  240 (2532 expanded)
%              Number of equality atoms :   58 ( 571 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_102,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => ( r1_tarski(k2_relat_1(B),A)
         => ( v1_funct_1(B)
            & v1_funct_2(B,k1_relat_1(B),A)
            & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B),A))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).

tff(f_39,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_33,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_49,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_45,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_89,axiom,(
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

tff(f_56,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_59,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(c_54,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_14,plain,(
    ! [B_7] : r1_tarski(B_7,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_50,plain,(
    r1_tarski(k2_relat_1('#skF_3'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_2593,plain,(
    ! [C_384,A_385,B_386] :
      ( m1_subset_1(C_384,k1_zfmisc_1(k2_zfmisc_1(A_385,B_386)))
      | ~ r1_tarski(k2_relat_1(C_384),B_386)
      | ~ r1_tarski(k1_relat_1(C_384),A_385)
      | ~ v1_relat_1(C_384) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_8,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_24,plain,(
    ! [A_10,B_11] :
      ( m1_subset_1(A_10,k1_zfmisc_1(B_11))
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_18,plain,(
    ! [A_8] : k2_zfmisc_1(A_8,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_36,plain,(
    ! [A_21] :
      ( v1_funct_2(k1_xboole_0,A_21,k1_xboole_0)
      | k1_xboole_0 = A_21
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(A_21,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_59,plain,(
    ! [A_21] :
      ( v1_funct_2(k1_xboole_0,A_21,k1_xboole_0)
      | k1_xboole_0 = A_21
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_36])).

tff(c_1075,plain,(
    ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitLeft,[status(thm)],[c_59])).

tff(c_1078,plain,(
    ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_24,c_1075])).

tff(c_1082,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_1078])).

tff(c_1084,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitRight,[status(thm)],[c_59])).

tff(c_26,plain,(
    ! [C_14,B_13,A_12] :
      ( ~ v1_xboole_0(C_14)
      | ~ m1_subset_1(B_13,k1_zfmisc_1(C_14))
      | ~ r2_hidden(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_1086,plain,(
    ! [A_12] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ r2_hidden(A_12,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_1084,c_26])).

tff(c_1095,plain,(
    ! [A_192] : ~ r2_hidden(A_192,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_1086])).

tff(c_1100,plain,(
    ! [B_2] : r1_tarski(k1_xboole_0,B_2) ),
    inference(resolution,[status(thm)],[c_6,c_1095])).

tff(c_130,plain,(
    ! [C_39,B_40,A_41] :
      ( ~ v1_xboole_0(C_39)
      | ~ m1_subset_1(B_40,k1_zfmisc_1(C_39))
      | ~ r2_hidden(A_41,B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_134,plain,(
    ! [B_42,A_43,A_44] :
      ( ~ v1_xboole_0(B_42)
      | ~ r2_hidden(A_43,A_44)
      | ~ r1_tarski(A_44,B_42) ) ),
    inference(resolution,[status(thm)],[c_24,c_130])).

tff(c_138,plain,(
    ! [B_45,A_46,B_47] :
      ( ~ v1_xboole_0(B_45)
      | ~ r1_tarski(A_46,B_45)
      | r1_tarski(A_46,B_47) ) ),
    inference(resolution,[status(thm)],[c_6,c_134])).

tff(c_145,plain,(
    ! [B_48,B_49] :
      ( ~ v1_xboole_0(B_48)
      | r1_tarski(B_48,B_49) ) ),
    inference(resolution,[status(thm)],[c_14,c_138])).

tff(c_108,plain,(
    ! [B_35,A_36] :
      ( B_35 = A_36
      | ~ r1_tarski(B_35,A_36)
      | ~ r1_tarski(A_36,B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_113,plain,
    ( k2_relat_1('#skF_3') = '#skF_2'
    | ~ r1_tarski('#skF_2',k2_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_50,c_108])).

tff(c_118,plain,(
    ~ r1_tarski('#skF_2',k2_relat_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_113])).

tff(c_154,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_145,c_118])).

tff(c_52,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_48,plain,
    ( ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2')))
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),'#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_56,plain,
    ( ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2')))
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_48])).

tff(c_93,plain,(
    ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_269,plain,(
    ! [C_68,A_69,B_70] :
      ( m1_subset_1(C_68,k1_zfmisc_1(k2_zfmisc_1(A_69,B_70)))
      | ~ r1_tarski(k2_relat_1(C_68),B_70)
      | ~ r1_tarski(k1_relat_1(C_68),A_69)
      | ~ v1_relat_1(C_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_22,plain,(
    ! [A_10,B_11] :
      ( r1_tarski(A_10,B_11)
      | ~ m1_subset_1(A_10,k1_zfmisc_1(B_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_664,plain,(
    ! [C_135,A_136,B_137] :
      ( r1_tarski(C_135,k2_zfmisc_1(A_136,B_137))
      | ~ r1_tarski(k2_relat_1(C_135),B_137)
      | ~ r1_tarski(k1_relat_1(C_135),A_136)
      | ~ v1_relat_1(C_135) ) ),
    inference(resolution,[status(thm)],[c_269,c_22])).

tff(c_669,plain,(
    ! [A_136] :
      ( r1_tarski('#skF_3',k2_zfmisc_1(A_136,'#skF_2'))
      | ~ r1_tarski(k1_relat_1('#skF_3'),A_136)
      | ~ v1_relat_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_50,c_664])).

tff(c_682,plain,(
    ! [A_138] :
      ( r1_tarski('#skF_3',k2_zfmisc_1(A_138,'#skF_2'))
      | ~ r1_tarski(k1_relat_1('#skF_3'),A_138) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_669])).

tff(c_692,plain,(
    r1_tarski('#skF_3',k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2')) ),
    inference(resolution,[status(thm)],[c_14,c_682])).

tff(c_184,plain,(
    ! [A_58,B_59,C_60] :
      ( k1_relset_1(A_58,B_59,C_60) = k1_relat_1(C_60)
      | ~ m1_subset_1(C_60,k1_zfmisc_1(k2_zfmisc_1(A_58,B_59))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_195,plain,(
    ! [A_58,B_59,A_10] :
      ( k1_relset_1(A_58,B_59,A_10) = k1_relat_1(A_10)
      | ~ r1_tarski(A_10,k2_zfmisc_1(A_58,B_59)) ) ),
    inference(resolution,[status(thm)],[c_24,c_184])).

tff(c_706,plain,(
    k1_relset_1(k1_relat_1('#skF_3'),'#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_692,c_195])).

tff(c_513,plain,(
    ! [B_113,C_114,A_115] :
      ( k1_xboole_0 = B_113
      | v1_funct_2(C_114,A_115,B_113)
      | k1_relset_1(A_115,B_113,C_114) != A_115
      | ~ m1_subset_1(C_114,k1_zfmisc_1(k2_zfmisc_1(A_115,B_113))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_953,plain,(
    ! [B_173,A_174,A_175] :
      ( k1_xboole_0 = B_173
      | v1_funct_2(A_174,A_175,B_173)
      | k1_relset_1(A_175,B_173,A_174) != A_175
      | ~ r1_tarski(A_174,k2_zfmisc_1(A_175,B_173)) ) ),
    inference(resolution,[status(thm)],[c_24,c_513])).

tff(c_959,plain,
    ( k1_xboole_0 = '#skF_2'
    | v1_funct_2('#skF_3',k1_relat_1('#skF_3'),'#skF_2')
    | k1_relset_1(k1_relat_1('#skF_3'),'#skF_2','#skF_3') != k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_692,c_953])).

tff(c_981,plain,
    ( k1_xboole_0 = '#skF_2'
    | v1_funct_2('#skF_3',k1_relat_1('#skF_3'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_706,c_959])).

tff(c_982,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_93,c_981])).

tff(c_1029,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_982,c_8])).

tff(c_1031,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_154,c_1029])).

tff(c_1032,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_113])).

tff(c_1187,plain,(
    ! [C_209,A_210,B_211] :
      ( m1_subset_1(C_209,k1_zfmisc_1(k2_zfmisc_1(A_210,B_211)))
      | ~ r1_tarski(k2_relat_1(C_209),B_211)
      | ~ r1_tarski(k1_relat_1(C_209),A_210)
      | ~ v1_relat_1(C_209) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_1593,plain,(
    ! [C_276,A_277,B_278] :
      ( r1_tarski(C_276,k2_zfmisc_1(A_277,B_278))
      | ~ r1_tarski(k2_relat_1(C_276),B_278)
      | ~ r1_tarski(k1_relat_1(C_276),A_277)
      | ~ v1_relat_1(C_276) ) ),
    inference(resolution,[status(thm)],[c_1187,c_22])).

tff(c_1740,plain,(
    ! [C_301,A_302] :
      ( r1_tarski(C_301,k2_zfmisc_1(A_302,k2_relat_1(C_301)))
      | ~ r1_tarski(k1_relat_1(C_301),A_302)
      | ~ v1_relat_1(C_301) ) ),
    inference(resolution,[status(thm)],[c_14,c_1593])).

tff(c_1764,plain,(
    ! [A_302] :
      ( r1_tarski('#skF_3',k2_zfmisc_1(A_302,'#skF_2'))
      | ~ r1_tarski(k1_relat_1('#skF_3'),A_302)
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1032,c_1740])).

tff(c_1794,plain,(
    ! [A_304] :
      ( r1_tarski('#skF_3',k2_zfmisc_1(A_304,'#skF_2'))
      | ~ r1_tarski(k1_relat_1('#skF_3'),A_304) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_1764])).

tff(c_1809,plain,(
    r1_tarski('#skF_3',k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2')) ),
    inference(resolution,[status(thm)],[c_14,c_1794])).

tff(c_1101,plain,(
    ! [A_193,B_194,C_195] :
      ( k1_relset_1(A_193,B_194,C_195) = k1_relat_1(C_195)
      | ~ m1_subset_1(C_195,k1_zfmisc_1(k2_zfmisc_1(A_193,B_194))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_1112,plain,(
    ! [A_193,B_194,A_10] :
      ( k1_relset_1(A_193,B_194,A_10) = k1_relat_1(A_10)
      | ~ r1_tarski(A_10,k2_zfmisc_1(A_193,B_194)) ) ),
    inference(resolution,[status(thm)],[c_24,c_1101])).

tff(c_1866,plain,(
    k1_relset_1(k1_relat_1('#skF_3'),'#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1809,c_1112])).

tff(c_1310,plain,(
    ! [B_229,C_230,A_231] :
      ( k1_xboole_0 = B_229
      | v1_funct_2(C_230,A_231,B_229)
      | k1_relset_1(A_231,B_229,C_230) != A_231
      | ~ m1_subset_1(C_230,k1_zfmisc_1(k2_zfmisc_1(A_231,B_229))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_1325,plain,(
    ! [B_229,A_10,A_231] :
      ( k1_xboole_0 = B_229
      | v1_funct_2(A_10,A_231,B_229)
      | k1_relset_1(A_231,B_229,A_10) != A_231
      | ~ r1_tarski(A_10,k2_zfmisc_1(A_231,B_229)) ) ),
    inference(resolution,[status(thm)],[c_24,c_1310])).

tff(c_1848,plain,
    ( k1_xboole_0 = '#skF_2'
    | v1_funct_2('#skF_3',k1_relat_1('#skF_3'),'#skF_2')
    | k1_relset_1(k1_relat_1('#skF_3'),'#skF_2','#skF_3') != k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1809,c_1325])).

tff(c_1864,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1(k1_relat_1('#skF_3'),'#skF_2','#skF_3') != k1_relat_1('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_93,c_1848])).

tff(c_1910,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1866,c_1864])).

tff(c_1421,plain,(
    ! [C_252,A_253] :
      ( m1_subset_1(C_252,k1_zfmisc_1(k1_xboole_0))
      | ~ r1_tarski(k2_relat_1(C_252),k1_xboole_0)
      | ~ r1_tarski(k1_relat_1(C_252),A_253)
      | ~ v1_relat_1(C_252) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_1187])).

tff(c_1426,plain,(
    ! [A_253] :
      ( m1_subset_1('#skF_3',k1_zfmisc_1(k1_xboole_0))
      | ~ r1_tarski('#skF_2',k1_xboole_0)
      | ~ r1_tarski(k1_relat_1('#skF_3'),A_253)
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1032,c_1421])).

tff(c_1431,plain,(
    ! [A_253] :
      ( m1_subset_1('#skF_3',k1_zfmisc_1(k1_xboole_0))
      | ~ r1_tarski('#skF_2',k1_xboole_0)
      | ~ r1_tarski(k1_relat_1('#skF_3'),A_253) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_1426])).

tff(c_1434,plain,(
    ~ r1_tarski('#skF_2',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_1431])).

tff(c_1925,plain,(
    ~ r1_tarski('#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1910,c_1434])).

tff(c_1953,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_1925])).

tff(c_1955,plain,(
    r1_tarski('#skF_2',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_1431])).

tff(c_10,plain,(
    ! [B_7,A_6] :
      ( B_7 = A_6
      | ~ r1_tarski(B_7,A_6)
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1973,plain,
    ( k1_xboole_0 = '#skF_2'
    | ~ r1_tarski(k1_xboole_0,'#skF_2') ),
    inference(resolution,[status(thm)],[c_1955,c_10])).

tff(c_1989,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1100,c_1973])).

tff(c_2015,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1989,c_8])).

tff(c_1954,plain,(
    ! [A_253] :
      ( ~ r1_tarski(k1_relat_1('#skF_3'),A_253)
      | m1_subset_1('#skF_3',k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(splitRight,[status(thm)],[c_1431])).

tff(c_2065,plain,(
    ! [A_253] :
      ( ~ r1_tarski(k1_relat_1('#skF_3'),A_253)
      | m1_subset_1('#skF_3',k1_zfmisc_1('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1989,c_1954])).

tff(c_2139,plain,(
    ! [A_318] : ~ r1_tarski(k1_relat_1('#skF_3'),A_318) ),
    inference(splitLeft,[status(thm)],[c_2065])).

tff(c_2149,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_14,c_2139])).

tff(c_2150,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_2065])).

tff(c_2184,plain,(
    r1_tarski('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_2150,c_22])).

tff(c_1056,plain,(
    ! [C_181,B_182,A_183] :
      ( ~ v1_xboole_0(C_181)
      | ~ m1_subset_1(B_182,k1_zfmisc_1(C_181))
      | ~ r2_hidden(A_183,B_182) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_1060,plain,(
    ! [B_184,A_185,A_186] :
      ( ~ v1_xboole_0(B_184)
      | ~ r2_hidden(A_185,A_186)
      | ~ r1_tarski(A_186,B_184) ) ),
    inference(resolution,[status(thm)],[c_24,c_1056])).

tff(c_1064,plain,(
    ! [B_187,A_188,B_189] :
      ( ~ v1_xboole_0(B_187)
      | ~ r1_tarski(A_188,B_187)
      | r1_tarski(A_188,B_189) ) ),
    inference(resolution,[status(thm)],[c_6,c_1060])).

tff(c_1068,plain,(
    ! [B_190,B_191] :
      ( ~ v1_xboole_0(B_190)
      | r1_tarski(B_190,B_191) ) ),
    inference(resolution,[status(thm)],[c_14,c_1064])).

tff(c_1074,plain,(
    ! [B_191,B_190] :
      ( B_191 = B_190
      | ~ r1_tarski(B_191,B_190)
      | ~ v1_xboole_0(B_190) ) ),
    inference(resolution,[status(thm)],[c_1068,c_10])).

tff(c_2200,plain,
    ( '#skF_2' = '#skF_3'
    | ~ v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_2184,c_1074])).

tff(c_2210,plain,(
    '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2015,c_2200])).

tff(c_30,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_20,plain,(
    ! [B_9] : k2_zfmisc_1(k1_xboole_0,B_9) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1171,plain,(
    ! [B_206,C_207] :
      ( k1_relset_1(k1_xboole_0,B_206,C_207) = k1_relat_1(C_207)
      | ~ m1_subset_1(C_207,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_1101])).

tff(c_1173,plain,(
    ! [B_206] : k1_relset_1(k1_xboole_0,B_206,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_1084,c_1171])).

tff(c_1178,plain,(
    ! [B_206] : k1_relset_1(k1_xboole_0,B_206,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_1173])).

tff(c_40,plain,(
    ! [C_23,B_22] :
      ( v1_funct_2(C_23,k1_xboole_0,B_22)
      | k1_relset_1(k1_xboole_0,B_22,C_23) != k1_xboole_0
      | ~ m1_subset_1(C_23,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_22))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_1264,plain,(
    ! [C_221,B_222] :
      ( v1_funct_2(C_221,k1_xboole_0,B_222)
      | k1_relset_1(k1_xboole_0,B_222,C_221) != k1_xboole_0
      | ~ m1_subset_1(C_221,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_40])).

tff(c_1266,plain,(
    ! [B_222] :
      ( v1_funct_2(k1_xboole_0,k1_xboole_0,B_222)
      | k1_relset_1(k1_xboole_0,B_222,k1_xboole_0) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_1084,c_1264])).

tff(c_1272,plain,(
    ! [B_222] : v1_funct_2(k1_xboole_0,k1_xboole_0,B_222) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1178,c_1266])).

tff(c_1997,plain,(
    ! [B_222] : v1_funct_2('#skF_2','#skF_2',B_222) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1989,c_1989,c_1272])).

tff(c_2332,plain,(
    ! [B_222] : v1_funct_2('#skF_3','#skF_3',B_222) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2210,c_2210,c_1997])).

tff(c_2014,plain,(
    k1_relat_1('#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1989,c_1989,c_30])).

tff(c_2222,plain,(
    k1_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2210,c_2210,c_2014])).

tff(c_2228,plain,(
    ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2210,c_93])).

tff(c_2335,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2332,c_2222,c_2228])).

tff(c_2336,plain,(
    ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_2601,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_3'),'#skF_2')
    | ~ r1_tarski(k1_relat_1('#skF_3'),k1_relat_1('#skF_3'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_2593,c_2336])).

tff(c_2616,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_14,c_50,c_2601])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 09:54:42 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.96/1.77  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.35/1.79  
% 4.35/1.79  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.35/1.79  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 4.35/1.79  
% 4.35/1.79  %Foreground sorts:
% 4.35/1.79  
% 4.35/1.79  
% 4.35/1.79  %Background operators:
% 4.35/1.79  
% 4.35/1.79  
% 4.35/1.79  %Foreground operators:
% 4.35/1.79  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.35/1.79  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.35/1.79  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.35/1.79  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.35/1.79  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.35/1.79  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.35/1.79  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.35/1.79  tff('#skF_2', type, '#skF_2': $i).
% 4.35/1.79  tff('#skF_3', type, '#skF_3': $i).
% 4.35/1.79  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 4.35/1.79  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.35/1.79  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.35/1.79  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.35/1.79  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.35/1.79  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.35/1.79  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.35/1.79  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.35/1.79  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.35/1.79  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.35/1.79  
% 4.49/1.81  tff(f_102, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(k2_relat_1(B), A) => ((v1_funct_1(B) & v1_funct_2(B, k1_relat_1(B), A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B), A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_funct_2)).
% 4.49/1.81  tff(f_39, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.49/1.81  tff(f_71, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_relset_1)).
% 4.49/1.81  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 4.49/1.81  tff(f_33, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 4.49/1.81  tff(f_49, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 4.49/1.82  tff(f_45, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 4.49/1.82  tff(f_89, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 4.49/1.82  tff(f_56, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 4.49/1.82  tff(f_63, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 4.49/1.82  tff(f_59, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 4.49/1.82  tff(c_54, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_102])).
% 4.49/1.82  tff(c_14, plain, (![B_7]: (r1_tarski(B_7, B_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.49/1.82  tff(c_50, plain, (r1_tarski(k2_relat_1('#skF_3'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_102])).
% 4.49/1.82  tff(c_2593, plain, (![C_384, A_385, B_386]: (m1_subset_1(C_384, k1_zfmisc_1(k2_zfmisc_1(A_385, B_386))) | ~r1_tarski(k2_relat_1(C_384), B_386) | ~r1_tarski(k1_relat_1(C_384), A_385) | ~v1_relat_1(C_384))), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.49/1.82  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.49/1.82  tff(c_8, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.49/1.82  tff(c_24, plain, (![A_10, B_11]: (m1_subset_1(A_10, k1_zfmisc_1(B_11)) | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.49/1.82  tff(c_18, plain, (![A_8]: (k2_zfmisc_1(A_8, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.49/1.82  tff(c_36, plain, (![A_21]: (v1_funct_2(k1_xboole_0, A_21, k1_xboole_0) | k1_xboole_0=A_21 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(A_21, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 4.49/1.82  tff(c_59, plain, (![A_21]: (v1_funct_2(k1_xboole_0, A_21, k1_xboole_0) | k1_xboole_0=A_21 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_36])).
% 4.49/1.82  tff(c_1075, plain, (~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0))), inference(splitLeft, [status(thm)], [c_59])).
% 4.49/1.82  tff(c_1078, plain, (~r1_tarski(k1_xboole_0, k1_xboole_0)), inference(resolution, [status(thm)], [c_24, c_1075])).
% 4.49/1.82  tff(c_1082, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14, c_1078])).
% 4.49/1.82  tff(c_1084, plain, (m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0))), inference(splitRight, [status(thm)], [c_59])).
% 4.49/1.82  tff(c_26, plain, (![C_14, B_13, A_12]: (~v1_xboole_0(C_14) | ~m1_subset_1(B_13, k1_zfmisc_1(C_14)) | ~r2_hidden(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.49/1.82  tff(c_1086, plain, (![A_12]: (~v1_xboole_0(k1_xboole_0) | ~r2_hidden(A_12, k1_xboole_0))), inference(resolution, [status(thm)], [c_1084, c_26])).
% 4.49/1.82  tff(c_1095, plain, (![A_192]: (~r2_hidden(A_192, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_1086])).
% 4.49/1.82  tff(c_1100, plain, (![B_2]: (r1_tarski(k1_xboole_0, B_2))), inference(resolution, [status(thm)], [c_6, c_1095])).
% 4.49/1.82  tff(c_130, plain, (![C_39, B_40, A_41]: (~v1_xboole_0(C_39) | ~m1_subset_1(B_40, k1_zfmisc_1(C_39)) | ~r2_hidden(A_41, B_40))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.49/1.82  tff(c_134, plain, (![B_42, A_43, A_44]: (~v1_xboole_0(B_42) | ~r2_hidden(A_43, A_44) | ~r1_tarski(A_44, B_42))), inference(resolution, [status(thm)], [c_24, c_130])).
% 4.49/1.82  tff(c_138, plain, (![B_45, A_46, B_47]: (~v1_xboole_0(B_45) | ~r1_tarski(A_46, B_45) | r1_tarski(A_46, B_47))), inference(resolution, [status(thm)], [c_6, c_134])).
% 4.49/1.82  tff(c_145, plain, (![B_48, B_49]: (~v1_xboole_0(B_48) | r1_tarski(B_48, B_49))), inference(resolution, [status(thm)], [c_14, c_138])).
% 4.49/1.82  tff(c_108, plain, (![B_35, A_36]: (B_35=A_36 | ~r1_tarski(B_35, A_36) | ~r1_tarski(A_36, B_35))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.49/1.82  tff(c_113, plain, (k2_relat_1('#skF_3')='#skF_2' | ~r1_tarski('#skF_2', k2_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_50, c_108])).
% 4.49/1.82  tff(c_118, plain, (~r1_tarski('#skF_2', k2_relat_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_113])).
% 4.49/1.82  tff(c_154, plain, (~v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_145, c_118])).
% 4.49/1.82  tff(c_52, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_102])).
% 4.49/1.82  tff(c_48, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2'))) | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), '#skF_2') | ~v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_102])).
% 4.49/1.82  tff(c_56, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2'))) | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_48])).
% 4.49/1.82  tff(c_93, plain, (~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), '#skF_2')), inference(splitLeft, [status(thm)], [c_56])).
% 4.49/1.82  tff(c_269, plain, (![C_68, A_69, B_70]: (m1_subset_1(C_68, k1_zfmisc_1(k2_zfmisc_1(A_69, B_70))) | ~r1_tarski(k2_relat_1(C_68), B_70) | ~r1_tarski(k1_relat_1(C_68), A_69) | ~v1_relat_1(C_68))), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.49/1.82  tff(c_22, plain, (![A_10, B_11]: (r1_tarski(A_10, B_11) | ~m1_subset_1(A_10, k1_zfmisc_1(B_11)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.49/1.82  tff(c_664, plain, (![C_135, A_136, B_137]: (r1_tarski(C_135, k2_zfmisc_1(A_136, B_137)) | ~r1_tarski(k2_relat_1(C_135), B_137) | ~r1_tarski(k1_relat_1(C_135), A_136) | ~v1_relat_1(C_135))), inference(resolution, [status(thm)], [c_269, c_22])).
% 4.49/1.82  tff(c_669, plain, (![A_136]: (r1_tarski('#skF_3', k2_zfmisc_1(A_136, '#skF_2')) | ~r1_tarski(k1_relat_1('#skF_3'), A_136) | ~v1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_50, c_664])).
% 4.49/1.82  tff(c_682, plain, (![A_138]: (r1_tarski('#skF_3', k2_zfmisc_1(A_138, '#skF_2')) | ~r1_tarski(k1_relat_1('#skF_3'), A_138))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_669])).
% 4.49/1.82  tff(c_692, plain, (r1_tarski('#skF_3', k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2'))), inference(resolution, [status(thm)], [c_14, c_682])).
% 4.49/1.82  tff(c_184, plain, (![A_58, B_59, C_60]: (k1_relset_1(A_58, B_59, C_60)=k1_relat_1(C_60) | ~m1_subset_1(C_60, k1_zfmisc_1(k2_zfmisc_1(A_58, B_59))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.49/1.82  tff(c_195, plain, (![A_58, B_59, A_10]: (k1_relset_1(A_58, B_59, A_10)=k1_relat_1(A_10) | ~r1_tarski(A_10, k2_zfmisc_1(A_58, B_59)))), inference(resolution, [status(thm)], [c_24, c_184])).
% 4.49/1.82  tff(c_706, plain, (k1_relset_1(k1_relat_1('#skF_3'), '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_692, c_195])).
% 4.49/1.82  tff(c_513, plain, (![B_113, C_114, A_115]: (k1_xboole_0=B_113 | v1_funct_2(C_114, A_115, B_113) | k1_relset_1(A_115, B_113, C_114)!=A_115 | ~m1_subset_1(C_114, k1_zfmisc_1(k2_zfmisc_1(A_115, B_113))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 4.49/1.82  tff(c_953, plain, (![B_173, A_174, A_175]: (k1_xboole_0=B_173 | v1_funct_2(A_174, A_175, B_173) | k1_relset_1(A_175, B_173, A_174)!=A_175 | ~r1_tarski(A_174, k2_zfmisc_1(A_175, B_173)))), inference(resolution, [status(thm)], [c_24, c_513])).
% 4.49/1.82  tff(c_959, plain, (k1_xboole_0='#skF_2' | v1_funct_2('#skF_3', k1_relat_1('#skF_3'), '#skF_2') | k1_relset_1(k1_relat_1('#skF_3'), '#skF_2', '#skF_3')!=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_692, c_953])).
% 4.49/1.82  tff(c_981, plain, (k1_xboole_0='#skF_2' | v1_funct_2('#skF_3', k1_relat_1('#skF_3'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_706, c_959])).
% 4.49/1.82  tff(c_982, plain, (k1_xboole_0='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_93, c_981])).
% 4.49/1.82  tff(c_1029, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_982, c_8])).
% 4.49/1.82  tff(c_1031, plain, $false, inference(negUnitSimplification, [status(thm)], [c_154, c_1029])).
% 4.49/1.82  tff(c_1032, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(splitRight, [status(thm)], [c_113])).
% 4.49/1.82  tff(c_1187, plain, (![C_209, A_210, B_211]: (m1_subset_1(C_209, k1_zfmisc_1(k2_zfmisc_1(A_210, B_211))) | ~r1_tarski(k2_relat_1(C_209), B_211) | ~r1_tarski(k1_relat_1(C_209), A_210) | ~v1_relat_1(C_209))), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.49/1.82  tff(c_1593, plain, (![C_276, A_277, B_278]: (r1_tarski(C_276, k2_zfmisc_1(A_277, B_278)) | ~r1_tarski(k2_relat_1(C_276), B_278) | ~r1_tarski(k1_relat_1(C_276), A_277) | ~v1_relat_1(C_276))), inference(resolution, [status(thm)], [c_1187, c_22])).
% 4.49/1.82  tff(c_1740, plain, (![C_301, A_302]: (r1_tarski(C_301, k2_zfmisc_1(A_302, k2_relat_1(C_301))) | ~r1_tarski(k1_relat_1(C_301), A_302) | ~v1_relat_1(C_301))), inference(resolution, [status(thm)], [c_14, c_1593])).
% 4.49/1.82  tff(c_1764, plain, (![A_302]: (r1_tarski('#skF_3', k2_zfmisc_1(A_302, '#skF_2')) | ~r1_tarski(k1_relat_1('#skF_3'), A_302) | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1032, c_1740])).
% 4.49/1.82  tff(c_1794, plain, (![A_304]: (r1_tarski('#skF_3', k2_zfmisc_1(A_304, '#skF_2')) | ~r1_tarski(k1_relat_1('#skF_3'), A_304))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_1764])).
% 4.49/1.82  tff(c_1809, plain, (r1_tarski('#skF_3', k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2'))), inference(resolution, [status(thm)], [c_14, c_1794])).
% 4.49/1.82  tff(c_1101, plain, (![A_193, B_194, C_195]: (k1_relset_1(A_193, B_194, C_195)=k1_relat_1(C_195) | ~m1_subset_1(C_195, k1_zfmisc_1(k2_zfmisc_1(A_193, B_194))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.49/1.82  tff(c_1112, plain, (![A_193, B_194, A_10]: (k1_relset_1(A_193, B_194, A_10)=k1_relat_1(A_10) | ~r1_tarski(A_10, k2_zfmisc_1(A_193, B_194)))), inference(resolution, [status(thm)], [c_24, c_1101])).
% 4.49/1.82  tff(c_1866, plain, (k1_relset_1(k1_relat_1('#skF_3'), '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_1809, c_1112])).
% 4.49/1.82  tff(c_1310, plain, (![B_229, C_230, A_231]: (k1_xboole_0=B_229 | v1_funct_2(C_230, A_231, B_229) | k1_relset_1(A_231, B_229, C_230)!=A_231 | ~m1_subset_1(C_230, k1_zfmisc_1(k2_zfmisc_1(A_231, B_229))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 4.49/1.82  tff(c_1325, plain, (![B_229, A_10, A_231]: (k1_xboole_0=B_229 | v1_funct_2(A_10, A_231, B_229) | k1_relset_1(A_231, B_229, A_10)!=A_231 | ~r1_tarski(A_10, k2_zfmisc_1(A_231, B_229)))), inference(resolution, [status(thm)], [c_24, c_1310])).
% 4.49/1.82  tff(c_1848, plain, (k1_xboole_0='#skF_2' | v1_funct_2('#skF_3', k1_relat_1('#skF_3'), '#skF_2') | k1_relset_1(k1_relat_1('#skF_3'), '#skF_2', '#skF_3')!=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_1809, c_1325])).
% 4.49/1.82  tff(c_1864, plain, (k1_xboole_0='#skF_2' | k1_relset_1(k1_relat_1('#skF_3'), '#skF_2', '#skF_3')!=k1_relat_1('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_93, c_1848])).
% 4.49/1.82  tff(c_1910, plain, (k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_1866, c_1864])).
% 4.49/1.82  tff(c_1421, plain, (![C_252, A_253]: (m1_subset_1(C_252, k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski(k2_relat_1(C_252), k1_xboole_0) | ~r1_tarski(k1_relat_1(C_252), A_253) | ~v1_relat_1(C_252))), inference(superposition, [status(thm), theory('equality')], [c_18, c_1187])).
% 4.49/1.82  tff(c_1426, plain, (![A_253]: (m1_subset_1('#skF_3', k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski('#skF_2', k1_xboole_0) | ~r1_tarski(k1_relat_1('#skF_3'), A_253) | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1032, c_1421])).
% 4.49/1.82  tff(c_1431, plain, (![A_253]: (m1_subset_1('#skF_3', k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski('#skF_2', k1_xboole_0) | ~r1_tarski(k1_relat_1('#skF_3'), A_253))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_1426])).
% 4.49/1.82  tff(c_1434, plain, (~r1_tarski('#skF_2', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_1431])).
% 4.49/1.82  tff(c_1925, plain, (~r1_tarski('#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1910, c_1434])).
% 4.49/1.82  tff(c_1953, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14, c_1925])).
% 4.49/1.82  tff(c_1955, plain, (r1_tarski('#skF_2', k1_xboole_0)), inference(splitRight, [status(thm)], [c_1431])).
% 4.49/1.82  tff(c_10, plain, (![B_7, A_6]: (B_7=A_6 | ~r1_tarski(B_7, A_6) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.49/1.82  tff(c_1973, plain, (k1_xboole_0='#skF_2' | ~r1_tarski(k1_xboole_0, '#skF_2')), inference(resolution, [status(thm)], [c_1955, c_10])).
% 4.49/1.82  tff(c_1989, plain, (k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_1100, c_1973])).
% 4.49/1.82  tff(c_2015, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1989, c_8])).
% 4.49/1.82  tff(c_1954, plain, (![A_253]: (~r1_tarski(k1_relat_1('#skF_3'), A_253) | m1_subset_1('#skF_3', k1_zfmisc_1(k1_xboole_0)))), inference(splitRight, [status(thm)], [c_1431])).
% 4.49/1.82  tff(c_2065, plain, (![A_253]: (~r1_tarski(k1_relat_1('#skF_3'), A_253) | m1_subset_1('#skF_3', k1_zfmisc_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_1989, c_1954])).
% 4.49/1.82  tff(c_2139, plain, (![A_318]: (~r1_tarski(k1_relat_1('#skF_3'), A_318))), inference(splitLeft, [status(thm)], [c_2065])).
% 4.49/1.82  tff(c_2149, plain, $false, inference(resolution, [status(thm)], [c_14, c_2139])).
% 4.49/1.82  tff(c_2150, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_2'))), inference(splitRight, [status(thm)], [c_2065])).
% 4.49/1.82  tff(c_2184, plain, (r1_tarski('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_2150, c_22])).
% 4.49/1.82  tff(c_1056, plain, (![C_181, B_182, A_183]: (~v1_xboole_0(C_181) | ~m1_subset_1(B_182, k1_zfmisc_1(C_181)) | ~r2_hidden(A_183, B_182))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.49/1.82  tff(c_1060, plain, (![B_184, A_185, A_186]: (~v1_xboole_0(B_184) | ~r2_hidden(A_185, A_186) | ~r1_tarski(A_186, B_184))), inference(resolution, [status(thm)], [c_24, c_1056])).
% 4.49/1.82  tff(c_1064, plain, (![B_187, A_188, B_189]: (~v1_xboole_0(B_187) | ~r1_tarski(A_188, B_187) | r1_tarski(A_188, B_189))), inference(resolution, [status(thm)], [c_6, c_1060])).
% 4.49/1.82  tff(c_1068, plain, (![B_190, B_191]: (~v1_xboole_0(B_190) | r1_tarski(B_190, B_191))), inference(resolution, [status(thm)], [c_14, c_1064])).
% 4.49/1.82  tff(c_1074, plain, (![B_191, B_190]: (B_191=B_190 | ~r1_tarski(B_191, B_190) | ~v1_xboole_0(B_190))), inference(resolution, [status(thm)], [c_1068, c_10])).
% 4.49/1.82  tff(c_2200, plain, ('#skF_2'='#skF_3' | ~v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_2184, c_1074])).
% 4.49/1.82  tff(c_2210, plain, ('#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_2015, c_2200])).
% 4.49/1.82  tff(c_30, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.49/1.82  tff(c_20, plain, (![B_9]: (k2_zfmisc_1(k1_xboole_0, B_9)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.49/1.82  tff(c_1171, plain, (![B_206, C_207]: (k1_relset_1(k1_xboole_0, B_206, C_207)=k1_relat_1(C_207) | ~m1_subset_1(C_207, k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_1101])).
% 4.49/1.82  tff(c_1173, plain, (![B_206]: (k1_relset_1(k1_xboole_0, B_206, k1_xboole_0)=k1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_1084, c_1171])).
% 4.49/1.82  tff(c_1178, plain, (![B_206]: (k1_relset_1(k1_xboole_0, B_206, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_30, c_1173])).
% 4.49/1.82  tff(c_40, plain, (![C_23, B_22]: (v1_funct_2(C_23, k1_xboole_0, B_22) | k1_relset_1(k1_xboole_0, B_22, C_23)!=k1_xboole_0 | ~m1_subset_1(C_23, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_22))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 4.49/1.82  tff(c_1264, plain, (![C_221, B_222]: (v1_funct_2(C_221, k1_xboole_0, B_222) | k1_relset_1(k1_xboole_0, B_222, C_221)!=k1_xboole_0 | ~m1_subset_1(C_221, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_40])).
% 4.49/1.82  tff(c_1266, plain, (![B_222]: (v1_funct_2(k1_xboole_0, k1_xboole_0, B_222) | k1_relset_1(k1_xboole_0, B_222, k1_xboole_0)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_1084, c_1264])).
% 4.49/1.82  tff(c_1272, plain, (![B_222]: (v1_funct_2(k1_xboole_0, k1_xboole_0, B_222))), inference(demodulation, [status(thm), theory('equality')], [c_1178, c_1266])).
% 4.49/1.82  tff(c_1997, plain, (![B_222]: (v1_funct_2('#skF_2', '#skF_2', B_222))), inference(demodulation, [status(thm), theory('equality')], [c_1989, c_1989, c_1272])).
% 4.49/1.82  tff(c_2332, plain, (![B_222]: (v1_funct_2('#skF_3', '#skF_3', B_222))), inference(demodulation, [status(thm), theory('equality')], [c_2210, c_2210, c_1997])).
% 4.49/1.82  tff(c_2014, plain, (k1_relat_1('#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_1989, c_1989, c_30])).
% 4.49/1.82  tff(c_2222, plain, (k1_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_2210, c_2210, c_2014])).
% 4.49/1.82  tff(c_2228, plain, (~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2210, c_93])).
% 4.49/1.82  tff(c_2335, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2332, c_2222, c_2228])).
% 4.49/1.82  tff(c_2336, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2')))), inference(splitRight, [status(thm)], [c_56])).
% 4.49/1.82  tff(c_2601, plain, (~r1_tarski(k2_relat_1('#skF_3'), '#skF_2') | ~r1_tarski(k1_relat_1('#skF_3'), k1_relat_1('#skF_3')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_2593, c_2336])).
% 4.49/1.82  tff(c_2616, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54, c_14, c_50, c_2601])).
% 4.49/1.82  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.49/1.82  
% 4.49/1.82  Inference rules
% 4.49/1.82  ----------------------
% 4.49/1.82  #Ref     : 0
% 4.49/1.82  #Sup     : 535
% 4.49/1.82  #Fact    : 0
% 4.49/1.82  #Define  : 0
% 4.49/1.82  #Split   : 15
% 4.49/1.82  #Chain   : 0
% 4.49/1.82  #Close   : 0
% 4.49/1.82  
% 4.49/1.82  Ordering : KBO
% 4.49/1.82  
% 4.49/1.82  Simplification rules
% 4.49/1.82  ----------------------
% 4.49/1.82  #Subsume      : 78
% 4.49/1.82  #Demod        : 559
% 4.49/1.82  #Tautology    : 229
% 4.49/1.82  #SimpNegUnit  : 3
% 4.49/1.82  #BackRed      : 121
% 4.49/1.82  
% 4.49/1.82  #Partial instantiations: 0
% 4.49/1.82  #Strategies tried      : 1
% 4.49/1.82  
% 4.49/1.82  Timing (in seconds)
% 4.49/1.82  ----------------------
% 4.49/1.82  Preprocessing        : 0.33
% 4.49/1.82  Parsing              : 0.18
% 4.49/1.82  CNF conversion       : 0.02
% 4.49/1.82  Main loop            : 0.65
% 4.49/1.82  Inferencing          : 0.22
% 4.49/1.82  Reduction            : 0.20
% 4.49/1.82  Demodulation         : 0.14
% 4.49/1.82  BG Simplification    : 0.03
% 4.49/1.82  Subsumption          : 0.14
% 4.49/1.82  Abstraction          : 0.03
% 4.49/1.82  MUC search           : 0.00
% 4.49/1.82  Cooper               : 0.00
% 4.49/1.82  Total                : 1.04
% 4.49/1.82  Index Insertion      : 0.00
% 4.49/1.82  Index Deletion       : 0.00
% 4.49/1.82  Index Matching       : 0.00
% 4.49/1.82  BG Taut test         : 0.00
%------------------------------------------------------------------------------
