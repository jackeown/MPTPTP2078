%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:42 EST 2020

% Result     : Theorem 2.34s
% Output     : CNFRefutation 2.34s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 353 expanded)
%              Number of leaves         :   26 ( 135 expanded)
%              Depth                    :   11
%              Number of atoms          :  183 (1202 expanded)
%              Number of equality atoms :   69 ( 442 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

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

tff(f_84,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_funct_2)).

tff(f_44,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_40,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
      <=> ! [B,C] :
            ( ( r2_hidden(B,k1_relat_1(A))
              & r2_hidden(C,k1_relat_1(A))
              & k1_funct_1(A,B) = k1_funct_1(A,C) )
           => B = C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_funct_1)).

tff(f_48,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_66,axiom,(
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

tff(c_28,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_54,plain,(
    ! [C_23,A_24,B_25] :
      ( v1_relat_1(C_23)
      | ~ m1_subset_1(C_23,k1_zfmisc_1(k2_zfmisc_1(A_24,B_25))) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_58,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_28,c_54])).

tff(c_32,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_59,plain,(
    ! [A_26] :
      ( '#skF_2'(A_26) != '#skF_1'(A_26)
      | v2_funct_1(A_26)
      | ~ v1_funct_1(A_26)
      | ~ v1_relat_1(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_34,plain,
    ( '#skF_5' != '#skF_6'
    | ~ v2_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_53,plain,(
    ~ v2_funct_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_34])).

tff(c_62,plain,
    ( '#skF_2'('#skF_4') != '#skF_1'('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_59,c_53])).

tff(c_65,plain,(
    '#skF_2'('#skF_4') != '#skF_1'('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_32,c_62])).

tff(c_30,plain,(
    v1_funct_2('#skF_4','#skF_3','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_69,plain,(
    ! [A_30,B_31,C_32] :
      ( k1_relset_1(A_30,B_31,C_32) = k1_relat_1(C_32)
      | ~ m1_subset_1(C_32,k1_zfmisc_1(k2_zfmisc_1(A_30,B_31))) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_73,plain,(
    k1_relset_1('#skF_3','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_28,c_69])).

tff(c_114,plain,(
    ! [B_45,A_46,C_47] :
      ( k1_xboole_0 = B_45
      | k1_relset_1(A_46,B_45,C_47) = A_46
      | ~ v1_funct_2(C_47,A_46,B_45)
      | ~ m1_subset_1(C_47,k1_zfmisc_1(k2_zfmisc_1(A_46,B_45))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_117,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_3','#skF_3','#skF_4') = '#skF_3'
    | ~ v1_funct_2('#skF_4','#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_114])).

tff(c_120,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_73,c_117])).

tff(c_121,plain,(
    k1_relat_1('#skF_4') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_120])).

tff(c_10,plain,(
    ! [A_1] :
      ( r2_hidden('#skF_1'(A_1),k1_relat_1(A_1))
      | v2_funct_1(A_1)
      | ~ v1_funct_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_129,plain,
    ( r2_hidden('#skF_1'('#skF_4'),'#skF_3')
    | v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_121,c_10])).

tff(c_136,plain,
    ( r2_hidden('#skF_1'('#skF_4'),'#skF_3')
    | v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_32,c_129])).

tff(c_137,plain,(
    r2_hidden('#skF_1'('#skF_4'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_53,c_136])).

tff(c_8,plain,(
    ! [A_1] :
      ( r2_hidden('#skF_2'(A_1),k1_relat_1(A_1))
      | v2_funct_1(A_1)
      | ~ v1_funct_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_126,plain,
    ( r2_hidden('#skF_2'('#skF_4'),'#skF_3')
    | v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_121,c_8])).

tff(c_133,plain,
    ( r2_hidden('#skF_2'('#skF_4'),'#skF_3')
    | v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_32,c_126])).

tff(c_134,plain,(
    r2_hidden('#skF_2'('#skF_4'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_53,c_133])).

tff(c_6,plain,(
    ! [A_1] :
      ( k1_funct_1(A_1,'#skF_2'(A_1)) = k1_funct_1(A_1,'#skF_1'(A_1))
      | v2_funct_1(A_1)
      | ~ v1_funct_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_52,plain,(
    ! [D_22,C_21] :
      ( v2_funct_1('#skF_4')
      | D_22 = C_21
      | k1_funct_1('#skF_4',D_22) != k1_funct_1('#skF_4',C_21)
      | ~ r2_hidden(D_22,'#skF_3')
      | ~ r2_hidden(C_21,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_93,plain,(
    ! [D_36,C_37] :
      ( D_36 = C_37
      | k1_funct_1('#skF_4',D_36) != k1_funct_1('#skF_4',C_37)
      | ~ r2_hidden(D_36,'#skF_3')
      | ~ r2_hidden(C_37,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_53,c_52])).

tff(c_99,plain,(
    ! [D_36] :
      ( D_36 = '#skF_2'('#skF_4')
      | k1_funct_1('#skF_4',D_36) != k1_funct_1('#skF_4','#skF_1'('#skF_4'))
      | ~ r2_hidden(D_36,'#skF_3')
      | ~ r2_hidden('#skF_2'('#skF_4'),'#skF_3')
      | v2_funct_1('#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_93])).

tff(c_104,plain,(
    ! [D_36] :
      ( D_36 = '#skF_2'('#skF_4')
      | k1_funct_1('#skF_4',D_36) != k1_funct_1('#skF_4','#skF_1'('#skF_4'))
      | ~ r2_hidden(D_36,'#skF_3')
      | ~ r2_hidden('#skF_2'('#skF_4'),'#skF_3')
      | v2_funct_1('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_32,c_99])).

tff(c_105,plain,(
    ! [D_36] :
      ( D_36 = '#skF_2'('#skF_4')
      | k1_funct_1('#skF_4',D_36) != k1_funct_1('#skF_4','#skF_1'('#skF_4'))
      | ~ r2_hidden(D_36,'#skF_3')
      | ~ r2_hidden('#skF_2'('#skF_4'),'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_53,c_104])).

tff(c_144,plain,(
    ! [D_36] :
      ( D_36 = '#skF_2'('#skF_4')
      | k1_funct_1('#skF_4',D_36) != k1_funct_1('#skF_4','#skF_1'('#skF_4'))
      | ~ r2_hidden(D_36,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_134,c_105])).

tff(c_147,plain,
    ( '#skF_2'('#skF_4') = '#skF_1'('#skF_4')
    | ~ r2_hidden('#skF_1'('#skF_4'),'#skF_3') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_144])).

tff(c_149,plain,(
    '#skF_2'('#skF_4') = '#skF_1'('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_137,c_147])).

tff(c_151,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_65,c_149])).

tff(c_153,plain,(
    k1_relat_1('#skF_4') != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_120])).

tff(c_152,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_120])).

tff(c_24,plain,(
    ! [B_15,C_16] :
      ( k1_relset_1(k1_xboole_0,B_15,C_16) = k1_xboole_0
      | ~ v1_funct_2(C_16,k1_xboole_0,B_15)
      | ~ m1_subset_1(C_16,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_15))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_173,plain,(
    ! [B_51,C_52] :
      ( k1_relset_1('#skF_3',B_51,C_52) = '#skF_3'
      | ~ v1_funct_2(C_52,'#skF_3',B_51)
      | ~ m1_subset_1(C_52,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_51))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_152,c_152,c_152,c_152,c_24])).

tff(c_176,plain,
    ( k1_relset_1('#skF_3','#skF_3','#skF_4') = '#skF_3'
    | ~ v1_funct_2('#skF_4','#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_173])).

tff(c_179,plain,(
    k1_relat_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_73,c_176])).

tff(c_181,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_153,c_179])).

tff(c_182,plain,(
    '#skF_5' != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_183,plain,(
    v2_funct_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_38,plain,
    ( r2_hidden('#skF_6','#skF_3')
    | ~ v2_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_185,plain,(
    r2_hidden('#skF_6','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_183,c_38])).

tff(c_194,plain,(
    ! [C_53,A_54,B_55] :
      ( v1_relat_1(C_53)
      | ~ m1_subset_1(C_53,k1_zfmisc_1(k2_zfmisc_1(A_54,B_55))) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_198,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_28,c_194])).

tff(c_204,plain,(
    ! [A_60,B_61,C_62] :
      ( k1_relset_1(A_60,B_61,C_62) = k1_relat_1(C_62)
      | ~ m1_subset_1(C_62,k1_zfmisc_1(k2_zfmisc_1(A_60,B_61))) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_208,plain,(
    k1_relset_1('#skF_3','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_28,c_204])).

tff(c_233,plain,(
    ! [B_73,A_74,C_75] :
      ( k1_xboole_0 = B_73
      | k1_relset_1(A_74,B_73,C_75) = A_74
      | ~ v1_funct_2(C_75,A_74,B_73)
      | ~ m1_subset_1(C_75,k1_zfmisc_1(k2_zfmisc_1(A_74,B_73))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_236,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_3','#skF_3','#skF_4') = '#skF_3'
    | ~ v1_funct_2('#skF_4','#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_233])).

tff(c_239,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_208,c_236])).

tff(c_240,plain,(
    k1_relat_1('#skF_4') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_239])).

tff(c_40,plain,
    ( r2_hidden('#skF_5','#skF_3')
    | ~ v2_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_187,plain,(
    r2_hidden('#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_183,c_40])).

tff(c_36,plain,
    ( k1_funct_1('#skF_4','#skF_5') = k1_funct_1('#skF_4','#skF_6')
    | ~ v2_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_189,plain,(
    k1_funct_1('#skF_4','#skF_5') = k1_funct_1('#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_183,c_36])).

tff(c_265,plain,(
    ! [C_76,B_77,A_78] :
      ( C_76 = B_77
      | k1_funct_1(A_78,C_76) != k1_funct_1(A_78,B_77)
      | ~ r2_hidden(C_76,k1_relat_1(A_78))
      | ~ r2_hidden(B_77,k1_relat_1(A_78))
      | ~ v2_funct_1(A_78)
      | ~ v1_funct_1(A_78)
      | ~ v1_relat_1(A_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_271,plain,(
    ! [B_77] :
      ( B_77 = '#skF_5'
      | k1_funct_1('#skF_4',B_77) != k1_funct_1('#skF_4','#skF_6')
      | ~ r2_hidden('#skF_5',k1_relat_1('#skF_4'))
      | ~ r2_hidden(B_77,k1_relat_1('#skF_4'))
      | ~ v2_funct_1('#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_189,c_265])).

tff(c_278,plain,(
    ! [B_79] :
      ( B_79 = '#skF_5'
      | k1_funct_1('#skF_4',B_79) != k1_funct_1('#skF_4','#skF_6')
      | ~ r2_hidden(B_79,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_198,c_32,c_183,c_240,c_187,c_240,c_271])).

tff(c_284,plain,(
    '#skF_5' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_185,c_278])).

tff(c_292,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_182,c_284])).

tff(c_294,plain,(
    k1_relat_1('#skF_4') != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_239])).

tff(c_293,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_239])).

tff(c_321,plain,(
    ! [B_85,C_86] :
      ( k1_relset_1('#skF_3',B_85,C_86) = '#skF_3'
      | ~ v1_funct_2(C_86,'#skF_3',B_85)
      | ~ m1_subset_1(C_86,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_85))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_293,c_293,c_293,c_293,c_24])).

tff(c_324,plain,
    ( k1_relset_1('#skF_3','#skF_3','#skF_4') = '#skF_3'
    | ~ v1_funct_2('#skF_4','#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_321])).

tff(c_327,plain,(
    k1_relat_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_208,c_324])).

tff(c_329,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_294,c_327])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:26:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.34/1.38  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.34/1.39  
% 2.34/1.39  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.34/1.39  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4
% 2.34/1.39  
% 2.34/1.39  %Foreground sorts:
% 2.34/1.39  
% 2.34/1.39  
% 2.34/1.39  %Background operators:
% 2.34/1.39  
% 2.34/1.39  
% 2.34/1.39  %Foreground operators:
% 2.34/1.39  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.34/1.39  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.34/1.39  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 2.34/1.39  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.34/1.39  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.34/1.39  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.34/1.39  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.34/1.39  tff('#skF_5', type, '#skF_5': $i).
% 2.34/1.39  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.34/1.39  tff('#skF_6', type, '#skF_6': $i).
% 2.34/1.39  tff('#skF_3', type, '#skF_3': $i).
% 2.34/1.39  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.34/1.39  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.34/1.39  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.34/1.39  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.34/1.39  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.34/1.39  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.34/1.39  tff('#skF_4', type, '#skF_4': $i).
% 2.34/1.39  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.34/1.39  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.34/1.39  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.34/1.39  
% 2.34/1.41  tff(f_84, negated_conjecture, ~(![A, B]: (((v1_funct_1(B) & v1_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (v2_funct_1(B) <=> (![C, D]: (((r2_hidden(C, A) & r2_hidden(D, A)) & (k1_funct_1(B, C) = k1_funct_1(B, D))) => (C = D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_funct_2)).
% 2.34/1.41  tff(f_44, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.34/1.41  tff(f_40, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) <=> (![B, C]: (((r2_hidden(B, k1_relat_1(A)) & r2_hidden(C, k1_relat_1(A))) & (k1_funct_1(A, B) = k1_funct_1(A, C))) => (B = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_funct_1)).
% 2.34/1.41  tff(f_48, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.34/1.41  tff(f_66, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 2.34/1.41  tff(c_28, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.34/1.41  tff(c_54, plain, (![C_23, A_24, B_25]: (v1_relat_1(C_23) | ~m1_subset_1(C_23, k1_zfmisc_1(k2_zfmisc_1(A_24, B_25))))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.34/1.41  tff(c_58, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_28, c_54])).
% 2.34/1.41  tff(c_32, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.34/1.41  tff(c_59, plain, (![A_26]: ('#skF_2'(A_26)!='#skF_1'(A_26) | v2_funct_1(A_26) | ~v1_funct_1(A_26) | ~v1_relat_1(A_26))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.34/1.41  tff(c_34, plain, ('#skF_5'!='#skF_6' | ~v2_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.34/1.41  tff(c_53, plain, (~v2_funct_1('#skF_4')), inference(splitLeft, [status(thm)], [c_34])).
% 2.34/1.41  tff(c_62, plain, ('#skF_2'('#skF_4')!='#skF_1'('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_59, c_53])).
% 2.34/1.41  tff(c_65, plain, ('#skF_2'('#skF_4')!='#skF_1'('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_32, c_62])).
% 2.34/1.41  tff(c_30, plain, (v1_funct_2('#skF_4', '#skF_3', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.34/1.41  tff(c_69, plain, (![A_30, B_31, C_32]: (k1_relset_1(A_30, B_31, C_32)=k1_relat_1(C_32) | ~m1_subset_1(C_32, k1_zfmisc_1(k2_zfmisc_1(A_30, B_31))))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.34/1.41  tff(c_73, plain, (k1_relset_1('#skF_3', '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_28, c_69])).
% 2.34/1.41  tff(c_114, plain, (![B_45, A_46, C_47]: (k1_xboole_0=B_45 | k1_relset_1(A_46, B_45, C_47)=A_46 | ~v1_funct_2(C_47, A_46, B_45) | ~m1_subset_1(C_47, k1_zfmisc_1(k2_zfmisc_1(A_46, B_45))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.34/1.41  tff(c_117, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_3', '#skF_3', '#skF_4')='#skF_3' | ~v1_funct_2('#skF_4', '#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_28, c_114])).
% 2.34/1.41  tff(c_120, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_30, c_73, c_117])).
% 2.34/1.41  tff(c_121, plain, (k1_relat_1('#skF_4')='#skF_3'), inference(splitLeft, [status(thm)], [c_120])).
% 2.34/1.41  tff(c_10, plain, (![A_1]: (r2_hidden('#skF_1'(A_1), k1_relat_1(A_1)) | v2_funct_1(A_1) | ~v1_funct_1(A_1) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.34/1.41  tff(c_129, plain, (r2_hidden('#skF_1'('#skF_4'), '#skF_3') | v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_121, c_10])).
% 2.34/1.41  tff(c_136, plain, (r2_hidden('#skF_1'('#skF_4'), '#skF_3') | v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_32, c_129])).
% 2.34/1.41  tff(c_137, plain, (r2_hidden('#skF_1'('#skF_4'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_53, c_136])).
% 2.34/1.41  tff(c_8, plain, (![A_1]: (r2_hidden('#skF_2'(A_1), k1_relat_1(A_1)) | v2_funct_1(A_1) | ~v1_funct_1(A_1) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.34/1.41  tff(c_126, plain, (r2_hidden('#skF_2'('#skF_4'), '#skF_3') | v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_121, c_8])).
% 2.34/1.41  tff(c_133, plain, (r2_hidden('#skF_2'('#skF_4'), '#skF_3') | v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_32, c_126])).
% 2.34/1.41  tff(c_134, plain, (r2_hidden('#skF_2'('#skF_4'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_53, c_133])).
% 2.34/1.41  tff(c_6, plain, (![A_1]: (k1_funct_1(A_1, '#skF_2'(A_1))=k1_funct_1(A_1, '#skF_1'(A_1)) | v2_funct_1(A_1) | ~v1_funct_1(A_1) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.34/1.41  tff(c_52, plain, (![D_22, C_21]: (v2_funct_1('#skF_4') | D_22=C_21 | k1_funct_1('#skF_4', D_22)!=k1_funct_1('#skF_4', C_21) | ~r2_hidden(D_22, '#skF_3') | ~r2_hidden(C_21, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.34/1.41  tff(c_93, plain, (![D_36, C_37]: (D_36=C_37 | k1_funct_1('#skF_4', D_36)!=k1_funct_1('#skF_4', C_37) | ~r2_hidden(D_36, '#skF_3') | ~r2_hidden(C_37, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_53, c_52])).
% 2.34/1.41  tff(c_99, plain, (![D_36]: (D_36='#skF_2'('#skF_4') | k1_funct_1('#skF_4', D_36)!=k1_funct_1('#skF_4', '#skF_1'('#skF_4')) | ~r2_hidden(D_36, '#skF_3') | ~r2_hidden('#skF_2'('#skF_4'), '#skF_3') | v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_6, c_93])).
% 2.34/1.41  tff(c_104, plain, (![D_36]: (D_36='#skF_2'('#skF_4') | k1_funct_1('#skF_4', D_36)!=k1_funct_1('#skF_4', '#skF_1'('#skF_4')) | ~r2_hidden(D_36, '#skF_3') | ~r2_hidden('#skF_2'('#skF_4'), '#skF_3') | v2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_32, c_99])).
% 2.34/1.41  tff(c_105, plain, (![D_36]: (D_36='#skF_2'('#skF_4') | k1_funct_1('#skF_4', D_36)!=k1_funct_1('#skF_4', '#skF_1'('#skF_4')) | ~r2_hidden(D_36, '#skF_3') | ~r2_hidden('#skF_2'('#skF_4'), '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_53, c_104])).
% 2.34/1.41  tff(c_144, plain, (![D_36]: (D_36='#skF_2'('#skF_4') | k1_funct_1('#skF_4', D_36)!=k1_funct_1('#skF_4', '#skF_1'('#skF_4')) | ~r2_hidden(D_36, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_134, c_105])).
% 2.34/1.41  tff(c_147, plain, ('#skF_2'('#skF_4')='#skF_1'('#skF_4') | ~r2_hidden('#skF_1'('#skF_4'), '#skF_3')), inference(reflexivity, [status(thm), theory('equality')], [c_144])).
% 2.34/1.41  tff(c_149, plain, ('#skF_2'('#skF_4')='#skF_1'('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_137, c_147])).
% 2.34/1.41  tff(c_151, plain, $false, inference(negUnitSimplification, [status(thm)], [c_65, c_149])).
% 2.34/1.41  tff(c_153, plain, (k1_relat_1('#skF_4')!='#skF_3'), inference(splitRight, [status(thm)], [c_120])).
% 2.34/1.41  tff(c_152, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_120])).
% 2.34/1.41  tff(c_24, plain, (![B_15, C_16]: (k1_relset_1(k1_xboole_0, B_15, C_16)=k1_xboole_0 | ~v1_funct_2(C_16, k1_xboole_0, B_15) | ~m1_subset_1(C_16, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_15))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.34/1.41  tff(c_173, plain, (![B_51, C_52]: (k1_relset_1('#skF_3', B_51, C_52)='#skF_3' | ~v1_funct_2(C_52, '#skF_3', B_51) | ~m1_subset_1(C_52, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_51))))), inference(demodulation, [status(thm), theory('equality')], [c_152, c_152, c_152, c_152, c_24])).
% 2.34/1.41  tff(c_176, plain, (k1_relset_1('#skF_3', '#skF_3', '#skF_4')='#skF_3' | ~v1_funct_2('#skF_4', '#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_28, c_173])).
% 2.34/1.41  tff(c_179, plain, (k1_relat_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_30, c_73, c_176])).
% 2.34/1.41  tff(c_181, plain, $false, inference(negUnitSimplification, [status(thm)], [c_153, c_179])).
% 2.34/1.41  tff(c_182, plain, ('#skF_5'!='#skF_6'), inference(splitRight, [status(thm)], [c_34])).
% 2.34/1.41  tff(c_183, plain, (v2_funct_1('#skF_4')), inference(splitRight, [status(thm)], [c_34])).
% 2.34/1.41  tff(c_38, plain, (r2_hidden('#skF_6', '#skF_3') | ~v2_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.34/1.41  tff(c_185, plain, (r2_hidden('#skF_6', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_183, c_38])).
% 2.34/1.41  tff(c_194, plain, (![C_53, A_54, B_55]: (v1_relat_1(C_53) | ~m1_subset_1(C_53, k1_zfmisc_1(k2_zfmisc_1(A_54, B_55))))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.34/1.41  tff(c_198, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_28, c_194])).
% 2.34/1.41  tff(c_204, plain, (![A_60, B_61, C_62]: (k1_relset_1(A_60, B_61, C_62)=k1_relat_1(C_62) | ~m1_subset_1(C_62, k1_zfmisc_1(k2_zfmisc_1(A_60, B_61))))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.34/1.41  tff(c_208, plain, (k1_relset_1('#skF_3', '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_28, c_204])).
% 2.34/1.41  tff(c_233, plain, (![B_73, A_74, C_75]: (k1_xboole_0=B_73 | k1_relset_1(A_74, B_73, C_75)=A_74 | ~v1_funct_2(C_75, A_74, B_73) | ~m1_subset_1(C_75, k1_zfmisc_1(k2_zfmisc_1(A_74, B_73))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.34/1.41  tff(c_236, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_3', '#skF_3', '#skF_4')='#skF_3' | ~v1_funct_2('#skF_4', '#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_28, c_233])).
% 2.34/1.41  tff(c_239, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_30, c_208, c_236])).
% 2.34/1.41  tff(c_240, plain, (k1_relat_1('#skF_4')='#skF_3'), inference(splitLeft, [status(thm)], [c_239])).
% 2.34/1.41  tff(c_40, plain, (r2_hidden('#skF_5', '#skF_3') | ~v2_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.34/1.41  tff(c_187, plain, (r2_hidden('#skF_5', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_183, c_40])).
% 2.34/1.41  tff(c_36, plain, (k1_funct_1('#skF_4', '#skF_5')=k1_funct_1('#skF_4', '#skF_6') | ~v2_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.34/1.41  tff(c_189, plain, (k1_funct_1('#skF_4', '#skF_5')=k1_funct_1('#skF_4', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_183, c_36])).
% 2.34/1.41  tff(c_265, plain, (![C_76, B_77, A_78]: (C_76=B_77 | k1_funct_1(A_78, C_76)!=k1_funct_1(A_78, B_77) | ~r2_hidden(C_76, k1_relat_1(A_78)) | ~r2_hidden(B_77, k1_relat_1(A_78)) | ~v2_funct_1(A_78) | ~v1_funct_1(A_78) | ~v1_relat_1(A_78))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.34/1.41  tff(c_271, plain, (![B_77]: (B_77='#skF_5' | k1_funct_1('#skF_4', B_77)!=k1_funct_1('#skF_4', '#skF_6') | ~r2_hidden('#skF_5', k1_relat_1('#skF_4')) | ~r2_hidden(B_77, k1_relat_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_189, c_265])).
% 2.34/1.41  tff(c_278, plain, (![B_79]: (B_79='#skF_5' | k1_funct_1('#skF_4', B_79)!=k1_funct_1('#skF_4', '#skF_6') | ~r2_hidden(B_79, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_198, c_32, c_183, c_240, c_187, c_240, c_271])).
% 2.34/1.41  tff(c_284, plain, ('#skF_5'='#skF_6'), inference(resolution, [status(thm)], [c_185, c_278])).
% 2.34/1.41  tff(c_292, plain, $false, inference(negUnitSimplification, [status(thm)], [c_182, c_284])).
% 2.34/1.41  tff(c_294, plain, (k1_relat_1('#skF_4')!='#skF_3'), inference(splitRight, [status(thm)], [c_239])).
% 2.34/1.41  tff(c_293, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_239])).
% 2.34/1.41  tff(c_321, plain, (![B_85, C_86]: (k1_relset_1('#skF_3', B_85, C_86)='#skF_3' | ~v1_funct_2(C_86, '#skF_3', B_85) | ~m1_subset_1(C_86, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_85))))), inference(demodulation, [status(thm), theory('equality')], [c_293, c_293, c_293, c_293, c_24])).
% 2.34/1.41  tff(c_324, plain, (k1_relset_1('#skF_3', '#skF_3', '#skF_4')='#skF_3' | ~v1_funct_2('#skF_4', '#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_28, c_321])).
% 2.34/1.41  tff(c_327, plain, (k1_relat_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_30, c_208, c_324])).
% 2.34/1.41  tff(c_329, plain, $false, inference(negUnitSimplification, [status(thm)], [c_294, c_327])).
% 2.34/1.41  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.34/1.41  
% 2.34/1.41  Inference rules
% 2.34/1.41  ----------------------
% 2.34/1.41  #Ref     : 3
% 2.34/1.41  #Sup     : 48
% 2.34/1.41  #Fact    : 0
% 2.34/1.41  #Define  : 0
% 2.34/1.41  #Split   : 3
% 2.34/1.41  #Chain   : 0
% 2.34/1.41  #Close   : 0
% 2.34/1.41  
% 2.34/1.41  Ordering : KBO
% 2.34/1.41  
% 2.34/1.41  Simplification rules
% 2.34/1.41  ----------------------
% 2.34/1.41  #Subsume      : 9
% 2.34/1.41  #Demod        : 95
% 2.34/1.41  #Tautology    : 39
% 2.34/1.41  #SimpNegUnit  : 9
% 2.34/1.41  #BackRed      : 14
% 2.34/1.41  
% 2.34/1.41  #Partial instantiations: 0
% 2.34/1.41  #Strategies tried      : 1
% 2.34/1.41  
% 2.34/1.41  Timing (in seconds)
% 2.34/1.41  ----------------------
% 2.34/1.41  Preprocessing        : 0.33
% 2.34/1.41  Parsing              : 0.17
% 2.34/1.41  CNF conversion       : 0.02
% 2.34/1.41  Main loop            : 0.23
% 2.34/1.41  Inferencing          : 0.09
% 2.34/1.41  Reduction            : 0.07
% 2.34/1.41  Demodulation         : 0.05
% 2.34/1.41  BG Simplification    : 0.02
% 2.34/1.41  Subsumption          : 0.04
% 2.34/1.41  Abstraction          : 0.01
% 2.34/1.41  MUC search           : 0.00
% 2.34/1.41  Cooper               : 0.00
% 2.34/1.41  Total                : 0.60
% 2.34/1.41  Index Insertion      : 0.00
% 2.34/1.41  Index Deletion       : 0.00
% 2.34/1.41  Index Matching       : 0.00
% 2.34/1.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------
