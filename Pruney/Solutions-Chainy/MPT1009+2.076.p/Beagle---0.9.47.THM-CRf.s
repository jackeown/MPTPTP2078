%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:52 EST 2020

% Result     : Theorem 5.69s
% Output     : CNFRefutation 5.82s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 150 expanded)
%              Number of leaves         :   47 (  73 expanded)
%              Depth                    :   11
%              Number of atoms          :  155 ( 307 expanded)
%              Number of equality atoms :   45 (  81 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k2_enumset1 > k1_relset_1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > k11_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k11_relat_1,type,(
    k11_relat_1: ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

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

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_137,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,k1_tarski(A),B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => r1_tarski(k7_relset_1(k1_tarski(A),B,D,C),k1_tarski(k1_funct_1(D,A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_funct_2)).

tff(f_83,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_125,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(k2_relat_1(B),A)
       => ( v1_funct_1(B)
          & v1_funct_2(B,k1_relat_1(B),A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B),A))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).

tff(f_95,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_87,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k7_relset_1(A,B,C,D),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relset_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_91,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

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

tff(f_55,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] : k11_relat_1(A,B) = k9_relat_1(A,k1_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_relat_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_42,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_40,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

tff(f_79,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r2_hidden(A,k1_relat_1(B))
       => k11_relat_1(B,A) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t117_funct_1)).

tff(c_78,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_3'),'#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_123,plain,(
    ! [C_60,A_61,B_62] :
      ( v1_relat_1(C_60)
      | ~ m1_subset_1(C_60,k1_zfmisc_1(k2_zfmisc_1(A_61,B_62))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_132,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_78,c_123])).

tff(c_82,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_431,plain,(
    ! [B_129,A_130] :
      ( m1_subset_1(B_129,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_129),A_130)))
      | ~ r1_tarski(k2_relat_1(B_129),A_130)
      | ~ v1_funct_1(B_129)
      | ~ v1_relat_1(B_129) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_54,plain,(
    ! [A_38,B_39,C_40,D_41] :
      ( k7_relset_1(A_38,B_39,C_40,D_41) = k9_relat_1(C_40,D_41)
      | ~ m1_subset_1(C_40,k1_zfmisc_1(k2_zfmisc_1(A_38,B_39))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_5130,plain,(
    ! [B_19348,A_19349,D_19350] :
      ( k7_relset_1(k1_relat_1(B_19348),A_19349,B_19348,D_19350) = k9_relat_1(B_19348,D_19350)
      | ~ r1_tarski(k2_relat_1(B_19348),A_19349)
      | ~ v1_funct_1(B_19348)
      | ~ v1_relat_1(B_19348) ) ),
    inference(resolution,[status(thm)],[c_431,c_54])).

tff(c_6018,plain,(
    ! [B_20965,D_20966] :
      ( k7_relset_1(k1_relat_1(B_20965),k2_relat_1(B_20965),B_20965,D_20966) = k9_relat_1(B_20965,D_20966)
      | ~ v1_funct_1(B_20965)
      | ~ v1_relat_1(B_20965) ) ),
    inference(resolution,[status(thm)],[c_6,c_5130])).

tff(c_68,plain,(
    ! [B_46,A_45] :
      ( m1_subset_1(B_46,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_46),A_45)))
      | ~ r1_tarski(k2_relat_1(B_46),A_45)
      | ~ v1_funct_1(B_46)
      | ~ v1_relat_1(B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_357,plain,(
    ! [A_122,B_123,C_124,D_125] :
      ( m1_subset_1(k7_relset_1(A_122,B_123,C_124,D_125),k1_zfmisc_1(B_123))
      | ~ m1_subset_1(C_124,k1_zfmisc_1(k2_zfmisc_1(A_122,B_123))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_32,plain,(
    ! [A_15,B_16] :
      ( r1_tarski(A_15,B_16)
      | ~ m1_subset_1(A_15,k1_zfmisc_1(B_16)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_491,plain,(
    ! [A_138,B_139,C_140,D_141] :
      ( r1_tarski(k7_relset_1(A_138,B_139,C_140,D_141),B_139)
      | ~ m1_subset_1(C_140,k1_zfmisc_1(k2_zfmisc_1(A_138,B_139))) ) ),
    inference(resolution,[status(thm)],[c_357,c_32])).

tff(c_502,plain,(
    ! [B_46,A_45,D_141] :
      ( r1_tarski(k7_relset_1(k1_relat_1(B_46),A_45,B_46,D_141),A_45)
      | ~ r1_tarski(k2_relat_1(B_46),A_45)
      | ~ v1_funct_1(B_46)
      | ~ v1_relat_1(B_46) ) ),
    inference(resolution,[status(thm)],[c_68,c_491])).

tff(c_6024,plain,(
    ! [B_20965,D_20966] :
      ( r1_tarski(k9_relat_1(B_20965,D_20966),k2_relat_1(B_20965))
      | ~ r1_tarski(k2_relat_1(B_20965),k2_relat_1(B_20965))
      | ~ v1_funct_1(B_20965)
      | ~ v1_relat_1(B_20965)
      | ~ v1_funct_1(B_20965)
      | ~ v1_relat_1(B_20965) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6018,c_502])).

tff(c_6094,plain,(
    ! [B_21111,D_21112] :
      ( r1_tarski(k9_relat_1(B_21111,D_21112),k2_relat_1(B_21111))
      | ~ v1_funct_1(B_21111)
      | ~ v1_relat_1(B_21111) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_6024])).

tff(c_76,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_80,plain,(
    v1_funct_2('#skF_6',k1_tarski('#skF_3'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_255,plain,(
    ! [A_95,B_96,C_97] :
      ( k1_relset_1(A_95,B_96,C_97) = k1_relat_1(C_97)
      | ~ m1_subset_1(C_97,k1_zfmisc_1(k2_zfmisc_1(A_95,B_96))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_264,plain,(
    k1_relset_1(k1_tarski('#skF_3'),'#skF_4','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_78,c_255])).

tff(c_947,plain,(
    ! [B_215,A_216,C_217] :
      ( k1_xboole_0 = B_215
      | k1_relset_1(A_216,B_215,C_217) = A_216
      | ~ v1_funct_2(C_217,A_216,B_215)
      | ~ m1_subset_1(C_217,k1_zfmisc_1(k2_zfmisc_1(A_216,B_215))) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_961,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1(k1_tarski('#skF_3'),'#skF_4','#skF_6') = k1_tarski('#skF_3')
    | ~ v1_funct_2('#skF_6',k1_tarski('#skF_3'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_78,c_947])).

tff(c_967,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_tarski('#skF_3') = k1_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_264,c_961])).

tff(c_968,plain,(
    k1_tarski('#skF_3') = k1_relat_1('#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_967])).

tff(c_36,plain,(
    ! [A_17,B_19] :
      ( k9_relat_1(A_17,k1_tarski(B_19)) = k11_relat_1(A_17,B_19)
      | ~ v1_relat_1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_1679,plain,(
    ! [A_3774] :
      ( k9_relat_1(A_3774,k1_relat_1('#skF_6')) = k11_relat_1(A_3774,'#skF_3')
      | ~ v1_relat_1(A_3774) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_968,c_36])).

tff(c_203,plain,(
    ! [B_83,A_84] :
      ( v4_relat_1(B_83,A_84)
      | ~ r1_tarski(k1_relat_1(B_83),A_84)
      | ~ v1_relat_1(B_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_213,plain,(
    ! [B_85] :
      ( v4_relat_1(B_85,k1_relat_1(B_85))
      | ~ v1_relat_1(B_85) ) ),
    inference(resolution,[status(thm)],[c_6,c_203])).

tff(c_44,plain,(
    ! [B_25,A_24] :
      ( k7_relat_1(B_25,A_24) = B_25
      | ~ v4_relat_1(B_25,A_24)
      | ~ v1_relat_1(B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_218,plain,(
    ! [B_86] :
      ( k7_relat_1(B_86,k1_relat_1(B_86)) = B_86
      | ~ v1_relat_1(B_86) ) ),
    inference(resolution,[status(thm)],[c_213,c_44])).

tff(c_42,plain,(
    ! [B_23,A_22] :
      ( k2_relat_1(k7_relat_1(B_23,A_22)) = k9_relat_1(B_23,A_22)
      | ~ v1_relat_1(B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_224,plain,(
    ! [B_86] :
      ( k9_relat_1(B_86,k1_relat_1(B_86)) = k2_relat_1(B_86)
      | ~ v1_relat_1(B_86)
      | ~ v1_relat_1(B_86) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_218,c_42])).

tff(c_1710,plain,
    ( k11_relat_1('#skF_6','#skF_3') = k2_relat_1('#skF_6')
    | ~ v1_relat_1('#skF_6')
    | ~ v1_relat_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_1679,c_224])).

tff(c_1733,plain,(
    k11_relat_1('#skF_6','#skF_3') = k2_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_132,c_132,c_1710])).

tff(c_87,plain,(
    ! [A_52] : k2_tarski(A_52,A_52) = k1_tarski(A_52) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_10,plain,(
    ! [D_8,A_3] : r2_hidden(D_8,k2_tarski(A_3,D_8)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_93,plain,(
    ! [A_52] : r2_hidden(A_52,k1_tarski(A_52)) ),
    inference(superposition,[status(thm),theory(equality)],[c_87,c_10])).

tff(c_985,plain,(
    r2_hidden('#skF_3',k1_relat_1('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_968,c_93])).

tff(c_46,plain,(
    ! [B_27,A_26] :
      ( k1_tarski(k1_funct_1(B_27,A_26)) = k11_relat_1(B_27,A_26)
      | ~ r2_hidden(A_26,k1_relat_1(B_27))
      | ~ v1_funct_1(B_27)
      | ~ v1_relat_1(B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_991,plain,
    ( k1_tarski(k1_funct_1('#skF_6','#skF_3')) = k11_relat_1('#skF_6','#skF_3')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_985,c_46])).

tff(c_994,plain,(
    k1_tarski(k1_funct_1('#skF_6','#skF_3')) = k11_relat_1('#skF_6','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_82,c_991])).

tff(c_326,plain,(
    ! [A_113,B_114,C_115,D_116] :
      ( k7_relset_1(A_113,B_114,C_115,D_116) = k9_relat_1(C_115,D_116)
      | ~ m1_subset_1(C_115,k1_zfmisc_1(k2_zfmisc_1(A_113,B_114))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_333,plain,(
    ! [D_116] : k7_relset_1(k1_tarski('#skF_3'),'#skF_4','#skF_6',D_116) = k9_relat_1('#skF_6',D_116) ),
    inference(resolution,[status(thm)],[c_78,c_326])).

tff(c_74,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski('#skF_3'),'#skF_4','#skF_6','#skF_5'),k1_tarski(k1_funct_1('#skF_6','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_334,plain,(
    ~ r1_tarski(k9_relat_1('#skF_6','#skF_5'),k1_tarski(k1_funct_1('#skF_6','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_333,c_74])).

tff(c_1046,plain,(
    ~ r1_tarski(k9_relat_1('#skF_6','#skF_5'),k11_relat_1('#skF_6','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_994,c_334])).

tff(c_1738,plain,(
    ~ r1_tarski(k9_relat_1('#skF_6','#skF_5'),k2_relat_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1733,c_1046])).

tff(c_6099,plain,
    ( ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_6094,c_1738])).

tff(c_6132,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_82,c_6099])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:02:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.69/2.27  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.82/2.28  
% 5.82/2.28  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.82/2.28  %$ v1_funct_2 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k2_enumset1 > k1_relset_1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > k11_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4
% 5.82/2.28  
% 5.82/2.28  %Foreground sorts:
% 5.82/2.28  
% 5.82/2.28  
% 5.82/2.28  %Background operators:
% 5.82/2.28  
% 5.82/2.28  
% 5.82/2.28  %Foreground operators:
% 5.82/2.28  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 5.82/2.28  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.82/2.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.82/2.28  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.82/2.28  tff(k1_tarski, type, k1_tarski: $i > $i).
% 5.82/2.28  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 5.82/2.28  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.82/2.28  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.82/2.28  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 5.82/2.28  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.82/2.28  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 5.82/2.28  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.82/2.28  tff('#skF_5', type, '#skF_5': $i).
% 5.82/2.28  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.82/2.28  tff(k11_relat_1, type, k11_relat_1: ($i * $i) > $i).
% 5.82/2.28  tff('#skF_6', type, '#skF_6': $i).
% 5.82/2.28  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 5.82/2.28  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 5.82/2.28  tff('#skF_3', type, '#skF_3': $i).
% 5.82/2.28  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 5.82/2.28  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 5.82/2.28  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.82/2.28  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 5.82/2.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.82/2.28  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.82/2.28  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.82/2.28  tff('#skF_4', type, '#skF_4': $i).
% 5.82/2.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.82/2.28  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 5.82/2.28  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.82/2.28  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.82/2.28  
% 5.82/2.31  tff(f_137, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, k1_tarski(A), B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => r1_tarski(k7_relset_1(k1_tarski(A), B, D, C), k1_tarski(k1_funct_1(D, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_funct_2)).
% 5.82/2.31  tff(f_83, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 5.82/2.31  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.82/2.31  tff(f_125, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(k2_relat_1(B), A) => ((v1_funct_1(B) & v1_funct_2(B, k1_relat_1(B), A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B), A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_funct_2)).
% 5.82/2.31  tff(f_95, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 5.82/2.31  tff(f_87, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k7_relset_1(A, B, C, D), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_relset_1)).
% 5.82/2.31  tff(f_50, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 5.82/2.31  tff(f_91, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 5.82/2.31  tff(f_113, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 5.82/2.31  tff(f_55, axiom, (![A]: (v1_relat_1(A) => (![B]: (k11_relat_1(A, B) = k9_relat_1(A, k1_tarski(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d16_relat_1)).
% 5.82/2.31  tff(f_61, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 5.82/2.31  tff(f_71, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 5.82/2.31  tff(f_65, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 5.82/2.31  tff(f_42, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 5.82/2.31  tff(f_40, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 5.82/2.31  tff(f_79, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r2_hidden(A, k1_relat_1(B)) => (k11_relat_1(B, A) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t117_funct_1)).
% 5.82/2.31  tff(c_78, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_3'), '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_137])).
% 5.82/2.31  tff(c_123, plain, (![C_60, A_61, B_62]: (v1_relat_1(C_60) | ~m1_subset_1(C_60, k1_zfmisc_1(k2_zfmisc_1(A_61, B_62))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 5.82/2.31  tff(c_132, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_78, c_123])).
% 5.82/2.31  tff(c_82, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_137])).
% 5.82/2.31  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.82/2.31  tff(c_431, plain, (![B_129, A_130]: (m1_subset_1(B_129, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_129), A_130))) | ~r1_tarski(k2_relat_1(B_129), A_130) | ~v1_funct_1(B_129) | ~v1_relat_1(B_129))), inference(cnfTransformation, [status(thm)], [f_125])).
% 5.82/2.31  tff(c_54, plain, (![A_38, B_39, C_40, D_41]: (k7_relset_1(A_38, B_39, C_40, D_41)=k9_relat_1(C_40, D_41) | ~m1_subset_1(C_40, k1_zfmisc_1(k2_zfmisc_1(A_38, B_39))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 5.82/2.31  tff(c_5130, plain, (![B_19348, A_19349, D_19350]: (k7_relset_1(k1_relat_1(B_19348), A_19349, B_19348, D_19350)=k9_relat_1(B_19348, D_19350) | ~r1_tarski(k2_relat_1(B_19348), A_19349) | ~v1_funct_1(B_19348) | ~v1_relat_1(B_19348))), inference(resolution, [status(thm)], [c_431, c_54])).
% 5.82/2.31  tff(c_6018, plain, (![B_20965, D_20966]: (k7_relset_1(k1_relat_1(B_20965), k2_relat_1(B_20965), B_20965, D_20966)=k9_relat_1(B_20965, D_20966) | ~v1_funct_1(B_20965) | ~v1_relat_1(B_20965))), inference(resolution, [status(thm)], [c_6, c_5130])).
% 5.82/2.31  tff(c_68, plain, (![B_46, A_45]: (m1_subset_1(B_46, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_46), A_45))) | ~r1_tarski(k2_relat_1(B_46), A_45) | ~v1_funct_1(B_46) | ~v1_relat_1(B_46))), inference(cnfTransformation, [status(thm)], [f_125])).
% 5.82/2.31  tff(c_357, plain, (![A_122, B_123, C_124, D_125]: (m1_subset_1(k7_relset_1(A_122, B_123, C_124, D_125), k1_zfmisc_1(B_123)) | ~m1_subset_1(C_124, k1_zfmisc_1(k2_zfmisc_1(A_122, B_123))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 5.82/2.31  tff(c_32, plain, (![A_15, B_16]: (r1_tarski(A_15, B_16) | ~m1_subset_1(A_15, k1_zfmisc_1(B_16)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 5.82/2.31  tff(c_491, plain, (![A_138, B_139, C_140, D_141]: (r1_tarski(k7_relset_1(A_138, B_139, C_140, D_141), B_139) | ~m1_subset_1(C_140, k1_zfmisc_1(k2_zfmisc_1(A_138, B_139))))), inference(resolution, [status(thm)], [c_357, c_32])).
% 5.82/2.31  tff(c_502, plain, (![B_46, A_45, D_141]: (r1_tarski(k7_relset_1(k1_relat_1(B_46), A_45, B_46, D_141), A_45) | ~r1_tarski(k2_relat_1(B_46), A_45) | ~v1_funct_1(B_46) | ~v1_relat_1(B_46))), inference(resolution, [status(thm)], [c_68, c_491])).
% 5.82/2.31  tff(c_6024, plain, (![B_20965, D_20966]: (r1_tarski(k9_relat_1(B_20965, D_20966), k2_relat_1(B_20965)) | ~r1_tarski(k2_relat_1(B_20965), k2_relat_1(B_20965)) | ~v1_funct_1(B_20965) | ~v1_relat_1(B_20965) | ~v1_funct_1(B_20965) | ~v1_relat_1(B_20965))), inference(superposition, [status(thm), theory('equality')], [c_6018, c_502])).
% 5.82/2.31  tff(c_6094, plain, (![B_21111, D_21112]: (r1_tarski(k9_relat_1(B_21111, D_21112), k2_relat_1(B_21111)) | ~v1_funct_1(B_21111) | ~v1_relat_1(B_21111))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_6024])).
% 5.82/2.31  tff(c_76, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_137])).
% 5.82/2.31  tff(c_80, plain, (v1_funct_2('#skF_6', k1_tarski('#skF_3'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_137])).
% 5.82/2.31  tff(c_255, plain, (![A_95, B_96, C_97]: (k1_relset_1(A_95, B_96, C_97)=k1_relat_1(C_97) | ~m1_subset_1(C_97, k1_zfmisc_1(k2_zfmisc_1(A_95, B_96))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 5.82/2.31  tff(c_264, plain, (k1_relset_1(k1_tarski('#skF_3'), '#skF_4', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_78, c_255])).
% 5.82/2.31  tff(c_947, plain, (![B_215, A_216, C_217]: (k1_xboole_0=B_215 | k1_relset_1(A_216, B_215, C_217)=A_216 | ~v1_funct_2(C_217, A_216, B_215) | ~m1_subset_1(C_217, k1_zfmisc_1(k2_zfmisc_1(A_216, B_215))))), inference(cnfTransformation, [status(thm)], [f_113])).
% 5.82/2.31  tff(c_961, plain, (k1_xboole_0='#skF_4' | k1_relset_1(k1_tarski('#skF_3'), '#skF_4', '#skF_6')=k1_tarski('#skF_3') | ~v1_funct_2('#skF_6', k1_tarski('#skF_3'), '#skF_4')), inference(resolution, [status(thm)], [c_78, c_947])).
% 5.82/2.31  tff(c_967, plain, (k1_xboole_0='#skF_4' | k1_tarski('#skF_3')=k1_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_264, c_961])).
% 5.82/2.31  tff(c_968, plain, (k1_tarski('#skF_3')=k1_relat_1('#skF_6')), inference(negUnitSimplification, [status(thm)], [c_76, c_967])).
% 5.82/2.31  tff(c_36, plain, (![A_17, B_19]: (k9_relat_1(A_17, k1_tarski(B_19))=k11_relat_1(A_17, B_19) | ~v1_relat_1(A_17))), inference(cnfTransformation, [status(thm)], [f_55])).
% 5.82/2.31  tff(c_1679, plain, (![A_3774]: (k9_relat_1(A_3774, k1_relat_1('#skF_6'))=k11_relat_1(A_3774, '#skF_3') | ~v1_relat_1(A_3774))), inference(superposition, [status(thm), theory('equality')], [c_968, c_36])).
% 5.82/2.31  tff(c_203, plain, (![B_83, A_84]: (v4_relat_1(B_83, A_84) | ~r1_tarski(k1_relat_1(B_83), A_84) | ~v1_relat_1(B_83))), inference(cnfTransformation, [status(thm)], [f_61])).
% 5.82/2.31  tff(c_213, plain, (![B_85]: (v4_relat_1(B_85, k1_relat_1(B_85)) | ~v1_relat_1(B_85))), inference(resolution, [status(thm)], [c_6, c_203])).
% 5.82/2.31  tff(c_44, plain, (![B_25, A_24]: (k7_relat_1(B_25, A_24)=B_25 | ~v4_relat_1(B_25, A_24) | ~v1_relat_1(B_25))), inference(cnfTransformation, [status(thm)], [f_71])).
% 5.82/2.31  tff(c_218, plain, (![B_86]: (k7_relat_1(B_86, k1_relat_1(B_86))=B_86 | ~v1_relat_1(B_86))), inference(resolution, [status(thm)], [c_213, c_44])).
% 5.82/2.31  tff(c_42, plain, (![B_23, A_22]: (k2_relat_1(k7_relat_1(B_23, A_22))=k9_relat_1(B_23, A_22) | ~v1_relat_1(B_23))), inference(cnfTransformation, [status(thm)], [f_65])).
% 5.82/2.31  tff(c_224, plain, (![B_86]: (k9_relat_1(B_86, k1_relat_1(B_86))=k2_relat_1(B_86) | ~v1_relat_1(B_86) | ~v1_relat_1(B_86))), inference(superposition, [status(thm), theory('equality')], [c_218, c_42])).
% 5.82/2.31  tff(c_1710, plain, (k11_relat_1('#skF_6', '#skF_3')=k2_relat_1('#skF_6') | ~v1_relat_1('#skF_6') | ~v1_relat_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_1679, c_224])).
% 5.82/2.31  tff(c_1733, plain, (k11_relat_1('#skF_6', '#skF_3')=k2_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_132, c_132, c_132, c_1710])).
% 5.82/2.31  tff(c_87, plain, (![A_52]: (k2_tarski(A_52, A_52)=k1_tarski(A_52))), inference(cnfTransformation, [status(thm)], [f_42])).
% 5.82/2.31  tff(c_10, plain, (![D_8, A_3]: (r2_hidden(D_8, k2_tarski(A_3, D_8)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 5.82/2.31  tff(c_93, plain, (![A_52]: (r2_hidden(A_52, k1_tarski(A_52)))), inference(superposition, [status(thm), theory('equality')], [c_87, c_10])).
% 5.82/2.31  tff(c_985, plain, (r2_hidden('#skF_3', k1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_968, c_93])).
% 5.82/2.31  tff(c_46, plain, (![B_27, A_26]: (k1_tarski(k1_funct_1(B_27, A_26))=k11_relat_1(B_27, A_26) | ~r2_hidden(A_26, k1_relat_1(B_27)) | ~v1_funct_1(B_27) | ~v1_relat_1(B_27))), inference(cnfTransformation, [status(thm)], [f_79])).
% 5.82/2.31  tff(c_991, plain, (k1_tarski(k1_funct_1('#skF_6', '#skF_3'))=k11_relat_1('#skF_6', '#skF_3') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_985, c_46])).
% 5.82/2.31  tff(c_994, plain, (k1_tarski(k1_funct_1('#skF_6', '#skF_3'))=k11_relat_1('#skF_6', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_132, c_82, c_991])).
% 5.82/2.31  tff(c_326, plain, (![A_113, B_114, C_115, D_116]: (k7_relset_1(A_113, B_114, C_115, D_116)=k9_relat_1(C_115, D_116) | ~m1_subset_1(C_115, k1_zfmisc_1(k2_zfmisc_1(A_113, B_114))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 5.82/2.31  tff(c_333, plain, (![D_116]: (k7_relset_1(k1_tarski('#skF_3'), '#skF_4', '#skF_6', D_116)=k9_relat_1('#skF_6', D_116))), inference(resolution, [status(thm)], [c_78, c_326])).
% 5.82/2.31  tff(c_74, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_3'), '#skF_4', '#skF_6', '#skF_5'), k1_tarski(k1_funct_1('#skF_6', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_137])).
% 5.82/2.31  tff(c_334, plain, (~r1_tarski(k9_relat_1('#skF_6', '#skF_5'), k1_tarski(k1_funct_1('#skF_6', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_333, c_74])).
% 5.82/2.31  tff(c_1046, plain, (~r1_tarski(k9_relat_1('#skF_6', '#skF_5'), k11_relat_1('#skF_6', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_994, c_334])).
% 5.82/2.31  tff(c_1738, plain, (~r1_tarski(k9_relat_1('#skF_6', '#skF_5'), k2_relat_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_1733, c_1046])).
% 5.82/2.31  tff(c_6099, plain, (~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_6094, c_1738])).
% 5.82/2.31  tff(c_6132, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_132, c_82, c_6099])).
% 5.82/2.31  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.82/2.31  
% 5.82/2.31  Inference rules
% 5.82/2.31  ----------------------
% 5.82/2.31  #Ref     : 0
% 5.82/2.31  #Sup     : 799
% 5.82/2.31  #Fact    : 8
% 5.82/2.31  #Define  : 0
% 5.82/2.31  #Split   : 8
% 5.82/2.31  #Chain   : 0
% 5.82/2.31  #Close   : 0
% 5.82/2.31  
% 5.82/2.31  Ordering : KBO
% 5.82/2.31  
% 5.82/2.31  Simplification rules
% 5.82/2.31  ----------------------
% 5.82/2.31  #Subsume      : 185
% 5.82/2.31  #Demod        : 329
% 5.82/2.31  #Tautology    : 205
% 5.82/2.31  #SimpNegUnit  : 6
% 5.82/2.31  #BackRed      : 12
% 5.82/2.31  
% 5.82/2.31  #Partial instantiations: 10308
% 5.82/2.31  #Strategies tried      : 1
% 5.82/2.31  
% 5.82/2.31  Timing (in seconds)
% 5.82/2.31  ----------------------
% 5.82/2.31  Preprocessing        : 0.41
% 5.82/2.31  Parsing              : 0.23
% 5.82/2.31  CNF conversion       : 0.03
% 5.82/2.31  Main loop            : 1.02
% 5.82/2.31  Inferencing          : 0.50
% 5.82/2.31  Reduction            : 0.27
% 5.82/2.31  Demodulation         : 0.20
% 5.82/2.31  BG Simplification    : 0.04
% 5.82/2.31  Subsumption          : 0.15
% 5.82/2.31  Abstraction          : 0.05
% 5.82/2.31  MUC search           : 0.00
% 5.82/2.31  Cooper               : 0.00
% 5.82/2.31  Total                : 1.48
% 5.82/2.31  Index Insertion      : 0.00
% 5.82/2.31  Index Deletion       : 0.00
% 5.82/2.31  Index Matching       : 0.00
% 5.82/2.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
