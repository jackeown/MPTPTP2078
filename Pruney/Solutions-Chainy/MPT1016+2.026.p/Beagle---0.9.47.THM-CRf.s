%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:44 EST 2020

% Result     : Theorem 2.30s
% Output     : CNFRefutation 2.47s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 369 expanded)
%              Number of leaves         :   28 ( 141 expanded)
%              Depth                    :   11
%              Number of atoms          :  192 (1232 expanded)
%              Number of equality atoms :   69 ( 442 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff(k2_funct_1,type,(
    k2_funct_1: $i > $i )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_34,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_103,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_funct_1(B)
          & v1_funct_2(B,A,A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
       => ( v2_funct_1(B)
        <=> ! [C,D] :
              ( ( r2_hidden(C,A)
                & r2_hidden(D,A)
                & k1_funct_1(B,C) = k1_funct_1(B,D) )
             => C = D ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_funct_2)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_49,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
      <=> ! [B,C] :
            ( ( r2_hidden(B,k1_relat_1(A))
              & r2_hidden(C,k1_relat_1(A))
              & k1_funct_1(A,B) = k1_funct_1(A,C) )
           => B = C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_funct_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_71,axiom,(
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

tff(c_4,plain,(
    ! [A_4,B_5] : v1_relat_1(k2_zfmisc_1(A_4,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_32,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_59,plain,(
    ! [B_31,A_32] :
      ( v1_relat_1(B_31)
      | ~ m1_subset_1(B_31,k1_zfmisc_1(A_32))
      | ~ v1_relat_1(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_62,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_3')) ),
    inference(resolution,[status(thm)],[c_32,c_59])).

tff(c_65,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_62])).

tff(c_36,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_66,plain,(
    ! [A_33] :
      ( '#skF_2'(A_33) != '#skF_1'(A_33)
      | v2_funct_1(A_33)
      | ~ v1_funct_1(A_33)
      | ~ v1_relat_1(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_38,plain,
    ( '#skF_5' != '#skF_6'
    | ~ v2_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_57,plain,(
    ~ v2_funct_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_38])).

tff(c_69,plain,
    ( '#skF_2'('#skF_4') != '#skF_1'('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_66,c_57])).

tff(c_72,plain,(
    '#skF_2'('#skF_4') != '#skF_1'('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_36,c_69])).

tff(c_34,plain,(
    v1_funct_2('#skF_4','#skF_3','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_76,plain,(
    ! [A_37,B_38,C_39] :
      ( k1_relset_1(A_37,B_38,C_39) = k1_relat_1(C_39)
      | ~ m1_subset_1(C_39,k1_zfmisc_1(k2_zfmisc_1(A_37,B_38))) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_80,plain,(
    k1_relset_1('#skF_3','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_32,c_76])).

tff(c_122,plain,(
    ! [B_52,A_53,C_54] :
      ( k1_xboole_0 = B_52
      | k1_relset_1(A_53,B_52,C_54) = A_53
      | ~ v1_funct_2(C_54,A_53,B_52)
      | ~ m1_subset_1(C_54,k1_zfmisc_1(k2_zfmisc_1(A_53,B_52))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_125,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_3','#skF_3','#skF_4') = '#skF_3'
    | ~ v1_funct_2('#skF_4','#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_122])).

tff(c_128,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_80,c_125])).

tff(c_129,plain,(
    k1_relat_1('#skF_4') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_128])).

tff(c_14,plain,(
    ! [A_6] :
      ( r2_hidden('#skF_1'(A_6),k1_relat_1(A_6))
      | v2_funct_1(A_6)
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_137,plain,
    ( r2_hidden('#skF_1'('#skF_4'),'#skF_3')
    | v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_129,c_14])).

tff(c_144,plain,
    ( r2_hidden('#skF_1'('#skF_4'),'#skF_3')
    | v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_36,c_137])).

tff(c_145,plain,(
    r2_hidden('#skF_1'('#skF_4'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_57,c_144])).

tff(c_12,plain,(
    ! [A_6] :
      ( r2_hidden('#skF_2'(A_6),k1_relat_1(A_6))
      | v2_funct_1(A_6)
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_134,plain,
    ( r2_hidden('#skF_2'('#skF_4'),'#skF_3')
    | v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_129,c_12])).

tff(c_141,plain,
    ( r2_hidden('#skF_2'('#skF_4'),'#skF_3')
    | v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_36,c_134])).

tff(c_142,plain,(
    r2_hidden('#skF_2'('#skF_4'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_57,c_141])).

tff(c_10,plain,(
    ! [A_6] :
      ( k1_funct_1(A_6,'#skF_2'(A_6)) = k1_funct_1(A_6,'#skF_1'(A_6))
      | v2_funct_1(A_6)
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_56,plain,(
    ! [D_28,C_27] :
      ( v2_funct_1('#skF_4')
      | D_28 = C_27
      | k1_funct_1('#skF_4',D_28) != k1_funct_1('#skF_4',C_27)
      | ~ r2_hidden(D_28,'#skF_3')
      | ~ r2_hidden(C_27,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_103,plain,(
    ! [D_47,C_48] :
      ( D_47 = C_48
      | k1_funct_1('#skF_4',D_47) != k1_funct_1('#skF_4',C_48)
      | ~ r2_hidden(D_47,'#skF_3')
      | ~ r2_hidden(C_48,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_57,c_56])).

tff(c_109,plain,(
    ! [D_47] :
      ( D_47 = '#skF_2'('#skF_4')
      | k1_funct_1('#skF_4',D_47) != k1_funct_1('#skF_4','#skF_1'('#skF_4'))
      | ~ r2_hidden(D_47,'#skF_3')
      | ~ r2_hidden('#skF_2'('#skF_4'),'#skF_3')
      | v2_funct_1('#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_103])).

tff(c_114,plain,(
    ! [D_47] :
      ( D_47 = '#skF_2'('#skF_4')
      | k1_funct_1('#skF_4',D_47) != k1_funct_1('#skF_4','#skF_1'('#skF_4'))
      | ~ r2_hidden(D_47,'#skF_3')
      | ~ r2_hidden('#skF_2'('#skF_4'),'#skF_3')
      | v2_funct_1('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_36,c_109])).

tff(c_115,plain,(
    ! [D_47] :
      ( D_47 = '#skF_2'('#skF_4')
      | k1_funct_1('#skF_4',D_47) != k1_funct_1('#skF_4','#skF_1'('#skF_4'))
      | ~ r2_hidden(D_47,'#skF_3')
      | ~ r2_hidden('#skF_2'('#skF_4'),'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_57,c_114])).

tff(c_152,plain,(
    ! [D_47] :
      ( D_47 = '#skF_2'('#skF_4')
      | k1_funct_1('#skF_4',D_47) != k1_funct_1('#skF_4','#skF_1'('#skF_4'))
      | ~ r2_hidden(D_47,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_115])).

tff(c_155,plain,
    ( '#skF_2'('#skF_4') = '#skF_1'('#skF_4')
    | ~ r2_hidden('#skF_1'('#skF_4'),'#skF_3') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_152])).

tff(c_157,plain,(
    '#skF_2'('#skF_4') = '#skF_1'('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_145,c_155])).

tff(c_159,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_157])).

tff(c_161,plain,(
    k1_relat_1('#skF_4') != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_128])).

tff(c_160,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_128])).

tff(c_26,plain,(
    ! [B_17,C_18] :
      ( k1_relset_1(k1_xboole_0,B_17,C_18) = k1_xboole_0
      | ~ v1_funct_2(C_18,k1_xboole_0,B_17)
      | ~ m1_subset_1(C_18,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_17))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_181,plain,(
    ! [B_58,C_59] :
      ( k1_relset_1('#skF_3',B_58,C_59) = '#skF_3'
      | ~ v1_funct_2(C_59,'#skF_3',B_58)
      | ~ m1_subset_1(C_59,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_58))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_160,c_160,c_160,c_160,c_26])).

tff(c_184,plain,
    ( k1_relset_1('#skF_3','#skF_3','#skF_4') = '#skF_3'
    | ~ v1_funct_2('#skF_4','#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_181])).

tff(c_187,plain,(
    k1_relat_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_80,c_184])).

tff(c_189,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_161,c_187])).

tff(c_190,plain,(
    '#skF_5' != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_191,plain,(
    v2_funct_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_42,plain,
    ( r2_hidden('#skF_6','#skF_3')
    | ~ v2_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_194,plain,(
    r2_hidden('#skF_6','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_191,c_42])).

tff(c_203,plain,(
    ! [B_62,A_63] :
      ( v1_relat_1(B_62)
      | ~ m1_subset_1(B_62,k1_zfmisc_1(A_63))
      | ~ v1_relat_1(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_206,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_3')) ),
    inference(resolution,[status(thm)],[c_32,c_203])).

tff(c_209,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_206])).

tff(c_214,plain,(
    ! [A_68,B_69,C_70] :
      ( k1_relset_1(A_68,B_69,C_70) = k1_relat_1(C_70)
      | ~ m1_subset_1(C_70,k1_zfmisc_1(k2_zfmisc_1(A_68,B_69))) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_218,plain,(
    k1_relset_1('#skF_3','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_32,c_214])).

tff(c_242,plain,(
    ! [B_81,A_82,C_83] :
      ( k1_xboole_0 = B_81
      | k1_relset_1(A_82,B_81,C_83) = A_82
      | ~ v1_funct_2(C_83,A_82,B_81)
      | ~ m1_subset_1(C_83,k1_zfmisc_1(k2_zfmisc_1(A_82,B_81))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_245,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_3','#skF_3','#skF_4') = '#skF_3'
    | ~ v1_funct_2('#skF_4','#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_242])).

tff(c_248,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_218,c_245])).

tff(c_249,plain,(
    k1_relat_1('#skF_4') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_248])).

tff(c_44,plain,
    ( r2_hidden('#skF_5','#skF_3')
    | ~ v2_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_196,plain,(
    r2_hidden('#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_191,c_44])).

tff(c_40,plain,
    ( k1_funct_1('#skF_4','#skF_5') = k1_funct_1('#skF_4','#skF_6')
    | ~ v2_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_198,plain,(
    k1_funct_1('#skF_4','#skF_5') = k1_funct_1('#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_191,c_40])).

tff(c_276,plain,(
    ! [C_84,B_85,A_86] :
      ( C_84 = B_85
      | k1_funct_1(A_86,C_84) != k1_funct_1(A_86,B_85)
      | ~ r2_hidden(C_84,k1_relat_1(A_86))
      | ~ r2_hidden(B_85,k1_relat_1(A_86))
      | ~ v2_funct_1(A_86)
      | ~ v1_funct_1(A_86)
      | ~ v1_relat_1(A_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_282,plain,(
    ! [B_85] :
      ( B_85 = '#skF_5'
      | k1_funct_1('#skF_4',B_85) != k1_funct_1('#skF_4','#skF_6')
      | ~ r2_hidden('#skF_5',k1_relat_1('#skF_4'))
      | ~ r2_hidden(B_85,k1_relat_1('#skF_4'))
      | ~ v2_funct_1('#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_198,c_276])).

tff(c_289,plain,(
    ! [B_87] :
      ( B_87 = '#skF_5'
      | k1_funct_1('#skF_4',B_87) != k1_funct_1('#skF_4','#skF_6')
      | ~ r2_hidden(B_87,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_209,c_36,c_191,c_249,c_196,c_249,c_282])).

tff(c_295,plain,(
    '#skF_5' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_194,c_289])).

tff(c_303,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_190,c_295])).

tff(c_305,plain,(
    k1_relat_1('#skF_4') != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_248])).

tff(c_304,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_248])).

tff(c_327,plain,(
    ! [B_91,C_92] :
      ( k1_relset_1('#skF_3',B_91,C_92) = '#skF_3'
      | ~ v1_funct_2(C_92,'#skF_3',B_91)
      | ~ m1_subset_1(C_92,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_91))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_304,c_304,c_304,c_304,c_26])).

tff(c_330,plain,
    ( k1_relset_1('#skF_3','#skF_3','#skF_4') = '#skF_3'
    | ~ v1_funct_2('#skF_4','#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_327])).

tff(c_333,plain,(
    k1_relat_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_218,c_330])).

tff(c_335,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_305,c_333])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:32:59 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.30/1.36  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.30/1.37  
% 2.30/1.37  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.30/1.37  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4
% 2.30/1.37  
% 2.30/1.37  %Foreground sorts:
% 2.30/1.37  
% 2.30/1.37  
% 2.30/1.37  %Background operators:
% 2.30/1.37  
% 2.30/1.37  
% 2.30/1.37  %Foreground operators:
% 2.30/1.37  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.30/1.37  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.30/1.37  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 2.30/1.37  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 2.30/1.37  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.30/1.37  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.30/1.37  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.30/1.37  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.30/1.37  tff('#skF_5', type, '#skF_5': $i).
% 2.30/1.37  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.30/1.37  tff('#skF_6', type, '#skF_6': $i).
% 2.30/1.37  tff('#skF_3', type, '#skF_3': $i).
% 2.30/1.37  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.30/1.37  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.30/1.37  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.30/1.37  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.30/1.37  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.30/1.37  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.30/1.37  tff('#skF_4', type, '#skF_4': $i).
% 2.30/1.37  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.30/1.37  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.30/1.37  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.30/1.37  
% 2.47/1.39  tff(f_34, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.47/1.39  tff(f_103, negated_conjecture, ~(![A, B]: (((v1_funct_1(B) & v1_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (v2_funct_1(B) <=> (![C, D]: (((r2_hidden(C, A) & r2_hidden(D, A)) & (k1_funct_1(B, C) = k1_funct_1(B, D))) => (C = D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_funct_2)).
% 2.47/1.39  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.47/1.39  tff(f_49, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) <=> (![B, C]: (((r2_hidden(B, k1_relat_1(A)) & r2_hidden(C, k1_relat_1(A))) & (k1_funct_1(A, B) = k1_funct_1(A, C))) => (B = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_funct_1)).
% 2.47/1.39  tff(f_53, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.47/1.39  tff(f_71, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 2.47/1.39  tff(c_4, plain, (![A_4, B_5]: (v1_relat_1(k2_zfmisc_1(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.47/1.39  tff(c_32, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.47/1.39  tff(c_59, plain, (![B_31, A_32]: (v1_relat_1(B_31) | ~m1_subset_1(B_31, k1_zfmisc_1(A_32)) | ~v1_relat_1(A_32))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.47/1.39  tff(c_62, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_3'))), inference(resolution, [status(thm)], [c_32, c_59])).
% 2.47/1.39  tff(c_65, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_62])).
% 2.47/1.39  tff(c_36, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.47/1.39  tff(c_66, plain, (![A_33]: ('#skF_2'(A_33)!='#skF_1'(A_33) | v2_funct_1(A_33) | ~v1_funct_1(A_33) | ~v1_relat_1(A_33))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.47/1.39  tff(c_38, plain, ('#skF_5'!='#skF_6' | ~v2_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.47/1.39  tff(c_57, plain, (~v2_funct_1('#skF_4')), inference(splitLeft, [status(thm)], [c_38])).
% 2.47/1.39  tff(c_69, plain, ('#skF_2'('#skF_4')!='#skF_1'('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_66, c_57])).
% 2.47/1.39  tff(c_72, plain, ('#skF_2'('#skF_4')!='#skF_1'('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_65, c_36, c_69])).
% 2.47/1.39  tff(c_34, plain, (v1_funct_2('#skF_4', '#skF_3', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.47/1.39  tff(c_76, plain, (![A_37, B_38, C_39]: (k1_relset_1(A_37, B_38, C_39)=k1_relat_1(C_39) | ~m1_subset_1(C_39, k1_zfmisc_1(k2_zfmisc_1(A_37, B_38))))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.47/1.39  tff(c_80, plain, (k1_relset_1('#skF_3', '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_32, c_76])).
% 2.47/1.39  tff(c_122, plain, (![B_52, A_53, C_54]: (k1_xboole_0=B_52 | k1_relset_1(A_53, B_52, C_54)=A_53 | ~v1_funct_2(C_54, A_53, B_52) | ~m1_subset_1(C_54, k1_zfmisc_1(k2_zfmisc_1(A_53, B_52))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.47/1.39  tff(c_125, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_3', '#skF_3', '#skF_4')='#skF_3' | ~v1_funct_2('#skF_4', '#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_32, c_122])).
% 2.47/1.39  tff(c_128, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_34, c_80, c_125])).
% 2.47/1.39  tff(c_129, plain, (k1_relat_1('#skF_4')='#skF_3'), inference(splitLeft, [status(thm)], [c_128])).
% 2.47/1.39  tff(c_14, plain, (![A_6]: (r2_hidden('#skF_1'(A_6), k1_relat_1(A_6)) | v2_funct_1(A_6) | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.47/1.39  tff(c_137, plain, (r2_hidden('#skF_1'('#skF_4'), '#skF_3') | v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_129, c_14])).
% 2.47/1.39  tff(c_144, plain, (r2_hidden('#skF_1'('#skF_4'), '#skF_3') | v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_65, c_36, c_137])).
% 2.47/1.39  tff(c_145, plain, (r2_hidden('#skF_1'('#skF_4'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_57, c_144])).
% 2.47/1.39  tff(c_12, plain, (![A_6]: (r2_hidden('#skF_2'(A_6), k1_relat_1(A_6)) | v2_funct_1(A_6) | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.47/1.39  tff(c_134, plain, (r2_hidden('#skF_2'('#skF_4'), '#skF_3') | v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_129, c_12])).
% 2.47/1.39  tff(c_141, plain, (r2_hidden('#skF_2'('#skF_4'), '#skF_3') | v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_65, c_36, c_134])).
% 2.47/1.39  tff(c_142, plain, (r2_hidden('#skF_2'('#skF_4'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_57, c_141])).
% 2.47/1.39  tff(c_10, plain, (![A_6]: (k1_funct_1(A_6, '#skF_2'(A_6))=k1_funct_1(A_6, '#skF_1'(A_6)) | v2_funct_1(A_6) | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.47/1.39  tff(c_56, plain, (![D_28, C_27]: (v2_funct_1('#skF_4') | D_28=C_27 | k1_funct_1('#skF_4', D_28)!=k1_funct_1('#skF_4', C_27) | ~r2_hidden(D_28, '#skF_3') | ~r2_hidden(C_27, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.47/1.39  tff(c_103, plain, (![D_47, C_48]: (D_47=C_48 | k1_funct_1('#skF_4', D_47)!=k1_funct_1('#skF_4', C_48) | ~r2_hidden(D_47, '#skF_3') | ~r2_hidden(C_48, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_57, c_56])).
% 2.47/1.39  tff(c_109, plain, (![D_47]: (D_47='#skF_2'('#skF_4') | k1_funct_1('#skF_4', D_47)!=k1_funct_1('#skF_4', '#skF_1'('#skF_4')) | ~r2_hidden(D_47, '#skF_3') | ~r2_hidden('#skF_2'('#skF_4'), '#skF_3') | v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_10, c_103])).
% 2.47/1.39  tff(c_114, plain, (![D_47]: (D_47='#skF_2'('#skF_4') | k1_funct_1('#skF_4', D_47)!=k1_funct_1('#skF_4', '#skF_1'('#skF_4')) | ~r2_hidden(D_47, '#skF_3') | ~r2_hidden('#skF_2'('#skF_4'), '#skF_3') | v2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_65, c_36, c_109])).
% 2.47/1.39  tff(c_115, plain, (![D_47]: (D_47='#skF_2'('#skF_4') | k1_funct_1('#skF_4', D_47)!=k1_funct_1('#skF_4', '#skF_1'('#skF_4')) | ~r2_hidden(D_47, '#skF_3') | ~r2_hidden('#skF_2'('#skF_4'), '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_57, c_114])).
% 2.47/1.39  tff(c_152, plain, (![D_47]: (D_47='#skF_2'('#skF_4') | k1_funct_1('#skF_4', D_47)!=k1_funct_1('#skF_4', '#skF_1'('#skF_4')) | ~r2_hidden(D_47, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_142, c_115])).
% 2.47/1.39  tff(c_155, plain, ('#skF_2'('#skF_4')='#skF_1'('#skF_4') | ~r2_hidden('#skF_1'('#skF_4'), '#skF_3')), inference(reflexivity, [status(thm), theory('equality')], [c_152])).
% 2.47/1.39  tff(c_157, plain, ('#skF_2'('#skF_4')='#skF_1'('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_145, c_155])).
% 2.47/1.39  tff(c_159, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_157])).
% 2.47/1.39  tff(c_161, plain, (k1_relat_1('#skF_4')!='#skF_3'), inference(splitRight, [status(thm)], [c_128])).
% 2.47/1.39  tff(c_160, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_128])).
% 2.47/1.39  tff(c_26, plain, (![B_17, C_18]: (k1_relset_1(k1_xboole_0, B_17, C_18)=k1_xboole_0 | ~v1_funct_2(C_18, k1_xboole_0, B_17) | ~m1_subset_1(C_18, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_17))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.47/1.39  tff(c_181, plain, (![B_58, C_59]: (k1_relset_1('#skF_3', B_58, C_59)='#skF_3' | ~v1_funct_2(C_59, '#skF_3', B_58) | ~m1_subset_1(C_59, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_58))))), inference(demodulation, [status(thm), theory('equality')], [c_160, c_160, c_160, c_160, c_26])).
% 2.47/1.39  tff(c_184, plain, (k1_relset_1('#skF_3', '#skF_3', '#skF_4')='#skF_3' | ~v1_funct_2('#skF_4', '#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_32, c_181])).
% 2.47/1.39  tff(c_187, plain, (k1_relat_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_34, c_80, c_184])).
% 2.47/1.39  tff(c_189, plain, $false, inference(negUnitSimplification, [status(thm)], [c_161, c_187])).
% 2.47/1.39  tff(c_190, plain, ('#skF_5'!='#skF_6'), inference(splitRight, [status(thm)], [c_38])).
% 2.47/1.39  tff(c_191, plain, (v2_funct_1('#skF_4')), inference(splitRight, [status(thm)], [c_38])).
% 2.47/1.39  tff(c_42, plain, (r2_hidden('#skF_6', '#skF_3') | ~v2_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.47/1.39  tff(c_194, plain, (r2_hidden('#skF_6', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_191, c_42])).
% 2.47/1.39  tff(c_203, plain, (![B_62, A_63]: (v1_relat_1(B_62) | ~m1_subset_1(B_62, k1_zfmisc_1(A_63)) | ~v1_relat_1(A_63))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.47/1.39  tff(c_206, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_3'))), inference(resolution, [status(thm)], [c_32, c_203])).
% 2.47/1.39  tff(c_209, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_206])).
% 2.47/1.39  tff(c_214, plain, (![A_68, B_69, C_70]: (k1_relset_1(A_68, B_69, C_70)=k1_relat_1(C_70) | ~m1_subset_1(C_70, k1_zfmisc_1(k2_zfmisc_1(A_68, B_69))))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.47/1.39  tff(c_218, plain, (k1_relset_1('#skF_3', '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_32, c_214])).
% 2.47/1.39  tff(c_242, plain, (![B_81, A_82, C_83]: (k1_xboole_0=B_81 | k1_relset_1(A_82, B_81, C_83)=A_82 | ~v1_funct_2(C_83, A_82, B_81) | ~m1_subset_1(C_83, k1_zfmisc_1(k2_zfmisc_1(A_82, B_81))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.47/1.39  tff(c_245, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_3', '#skF_3', '#skF_4')='#skF_3' | ~v1_funct_2('#skF_4', '#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_32, c_242])).
% 2.47/1.39  tff(c_248, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_34, c_218, c_245])).
% 2.47/1.39  tff(c_249, plain, (k1_relat_1('#skF_4')='#skF_3'), inference(splitLeft, [status(thm)], [c_248])).
% 2.47/1.39  tff(c_44, plain, (r2_hidden('#skF_5', '#skF_3') | ~v2_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.47/1.39  tff(c_196, plain, (r2_hidden('#skF_5', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_191, c_44])).
% 2.47/1.39  tff(c_40, plain, (k1_funct_1('#skF_4', '#skF_5')=k1_funct_1('#skF_4', '#skF_6') | ~v2_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.47/1.39  tff(c_198, plain, (k1_funct_1('#skF_4', '#skF_5')=k1_funct_1('#skF_4', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_191, c_40])).
% 2.47/1.39  tff(c_276, plain, (![C_84, B_85, A_86]: (C_84=B_85 | k1_funct_1(A_86, C_84)!=k1_funct_1(A_86, B_85) | ~r2_hidden(C_84, k1_relat_1(A_86)) | ~r2_hidden(B_85, k1_relat_1(A_86)) | ~v2_funct_1(A_86) | ~v1_funct_1(A_86) | ~v1_relat_1(A_86))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.47/1.39  tff(c_282, plain, (![B_85]: (B_85='#skF_5' | k1_funct_1('#skF_4', B_85)!=k1_funct_1('#skF_4', '#skF_6') | ~r2_hidden('#skF_5', k1_relat_1('#skF_4')) | ~r2_hidden(B_85, k1_relat_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_198, c_276])).
% 2.47/1.39  tff(c_289, plain, (![B_87]: (B_87='#skF_5' | k1_funct_1('#skF_4', B_87)!=k1_funct_1('#skF_4', '#skF_6') | ~r2_hidden(B_87, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_209, c_36, c_191, c_249, c_196, c_249, c_282])).
% 2.47/1.39  tff(c_295, plain, ('#skF_5'='#skF_6'), inference(resolution, [status(thm)], [c_194, c_289])).
% 2.47/1.39  tff(c_303, plain, $false, inference(negUnitSimplification, [status(thm)], [c_190, c_295])).
% 2.47/1.39  tff(c_305, plain, (k1_relat_1('#skF_4')!='#skF_3'), inference(splitRight, [status(thm)], [c_248])).
% 2.47/1.39  tff(c_304, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_248])).
% 2.47/1.39  tff(c_327, plain, (![B_91, C_92]: (k1_relset_1('#skF_3', B_91, C_92)='#skF_3' | ~v1_funct_2(C_92, '#skF_3', B_91) | ~m1_subset_1(C_92, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_91))))), inference(demodulation, [status(thm), theory('equality')], [c_304, c_304, c_304, c_304, c_26])).
% 2.47/1.39  tff(c_330, plain, (k1_relset_1('#skF_3', '#skF_3', '#skF_4')='#skF_3' | ~v1_funct_2('#skF_4', '#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_32, c_327])).
% 2.47/1.39  tff(c_333, plain, (k1_relat_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_34, c_218, c_330])).
% 2.47/1.39  tff(c_335, plain, $false, inference(negUnitSimplification, [status(thm)], [c_305, c_333])).
% 2.47/1.39  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.47/1.39  
% 2.47/1.39  Inference rules
% 2.47/1.39  ----------------------
% 2.47/1.39  #Ref     : 3
% 2.47/1.39  #Sup     : 47
% 2.47/1.39  #Fact    : 0
% 2.47/1.39  #Define  : 0
% 2.47/1.39  #Split   : 4
% 2.47/1.39  #Chain   : 0
% 2.47/1.39  #Close   : 0
% 2.47/1.39  
% 2.47/1.39  Ordering : KBO
% 2.47/1.39  
% 2.47/1.39  Simplification rules
% 2.47/1.39  ----------------------
% 2.47/1.39  #Subsume      : 8
% 2.47/1.39  #Demod        : 96
% 2.47/1.39  #Tautology    : 40
% 2.47/1.39  #SimpNegUnit  : 9
% 2.47/1.39  #BackRed      : 14
% 2.47/1.39  
% 2.47/1.39  #Partial instantiations: 0
% 2.47/1.39  #Strategies tried      : 1
% 2.47/1.39  
% 2.47/1.39  Timing (in seconds)
% 2.47/1.39  ----------------------
% 2.47/1.40  Preprocessing        : 0.30
% 2.47/1.40  Parsing              : 0.15
% 2.47/1.40  CNF conversion       : 0.02
% 2.47/1.40  Main loop            : 0.23
% 2.47/1.40  Inferencing          : 0.08
% 2.47/1.40  Reduction            : 0.07
% 2.47/1.40  Demodulation         : 0.05
% 2.47/1.40  BG Simplification    : 0.02
% 2.47/1.40  Subsumption          : 0.04
% 2.47/1.40  Abstraction          : 0.01
% 2.47/1.40  MUC search           : 0.00
% 2.47/1.40  Cooper               : 0.00
% 2.47/1.40  Total                : 0.57
% 2.47/1.40  Index Insertion      : 0.00
% 2.47/1.40  Index Deletion       : 0.00
% 2.47/1.40  Index Matching       : 0.00
% 2.47/1.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------
