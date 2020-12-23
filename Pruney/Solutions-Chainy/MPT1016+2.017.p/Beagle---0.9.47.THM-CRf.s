%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:43 EST 2020

% Result     : Theorem 5.37s
% Output     : CNFRefutation 5.52s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 273 expanded)
%              Number of leaves         :   33 ( 105 expanded)
%              Depth                    :   11
%              Number of atoms          :  208 ( 933 expanded)
%              Number of equality atoms :   54 ( 238 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(f_108,negated_conjecture,(
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

tff(f_68,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_59,axiom,(
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

tff(f_76,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_72,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k1_relset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_relset_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_90,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( v2_funct_1(D)
          & r2_hidden(C,A) )
       => ( B = k1_xboole_0
          | k1_funct_1(k2_funct_1(D),k1_funct_1(D,C)) = C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_funct_2)).

tff(f_34,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_64,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_36,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_34,plain,(
    v1_funct_2('#skF_4','#skF_3','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_38,plain,
    ( '#skF_5' != '#skF_6'
    | ~ v2_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_57,plain,(
    ~ v2_funct_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_38])).

tff(c_32,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_75,plain,(
    ! [C_47,A_48,B_49] :
      ( v1_relat_1(C_47)
      | ~ m1_subset_1(C_47,k1_zfmisc_1(k2_zfmisc_1(A_48,B_49))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_88,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_32,c_75])).

tff(c_90,plain,(
    ! [A_50] :
      ( '#skF_2'(A_50) != '#skF_1'(A_50)
      | v2_funct_1(A_50)
      | ~ v1_funct_1(A_50)
      | ~ v1_relat_1(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_93,plain,
    ( '#skF_2'('#skF_4') != '#skF_1'('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_90,c_57])).

tff(c_96,plain,
    ( '#skF_2'('#skF_4') != '#skF_1'('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_93])).

tff(c_98,plain,(
    '#skF_2'('#skF_4') != '#skF_1'('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_96])).

tff(c_273,plain,(
    ! [A_85] :
      ( k1_funct_1(A_85,'#skF_2'(A_85)) = k1_funct_1(A_85,'#skF_1'(A_85))
      | v2_funct_1(A_85)
      | ~ v1_funct_1(A_85)
      | ~ v1_relat_1(A_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_56,plain,(
    ! [D_38,C_37] :
      ( v2_funct_1('#skF_4')
      | D_38 = C_37
      | k1_funct_1('#skF_4',D_38) != k1_funct_1('#skF_4',C_37)
      | ~ r2_hidden(D_38,'#skF_3')
      | ~ r2_hidden(C_37,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_99,plain,(
    ! [D_38,C_37] :
      ( D_38 = C_37
      | k1_funct_1('#skF_4',D_38) != k1_funct_1('#skF_4',C_37)
      | ~ r2_hidden(D_38,'#skF_3')
      | ~ r2_hidden(C_37,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_57,c_56])).

tff(c_279,plain,(
    ! [C_37] :
      ( C_37 = '#skF_2'('#skF_4')
      | k1_funct_1('#skF_4',C_37) != k1_funct_1('#skF_4','#skF_1'('#skF_4'))
      | ~ r2_hidden('#skF_2'('#skF_4'),'#skF_3')
      | ~ r2_hidden(C_37,'#skF_3')
      | v2_funct_1('#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_273,c_99])).

tff(c_288,plain,(
    ! [C_37] :
      ( C_37 = '#skF_2'('#skF_4')
      | k1_funct_1('#skF_4',C_37) != k1_funct_1('#skF_4','#skF_1'('#skF_4'))
      | ~ r2_hidden('#skF_2'('#skF_4'),'#skF_3')
      | ~ r2_hidden(C_37,'#skF_3')
      | v2_funct_1('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_36,c_279])).

tff(c_289,plain,(
    ! [C_37] :
      ( C_37 = '#skF_2'('#skF_4')
      | k1_funct_1('#skF_4',C_37) != k1_funct_1('#skF_4','#skF_1'('#skF_4'))
      | ~ r2_hidden('#skF_2'('#skF_4'),'#skF_3')
      | ~ r2_hidden(C_37,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_57,c_288])).

tff(c_381,plain,(
    ~ r2_hidden('#skF_2'('#skF_4'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_289])).

tff(c_155,plain,(
    ! [A_72,B_73,C_74] :
      ( k1_relset_1(A_72,B_73,C_74) = k1_relat_1(C_74)
      | ~ m1_subset_1(C_74,k1_zfmisc_1(k2_zfmisc_1(A_72,B_73))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_168,plain,(
    k1_relset_1('#skF_3','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_32,c_155])).

tff(c_193,plain,(
    ! [A_80,B_81,C_82] :
      ( m1_subset_1(k1_relset_1(A_80,B_81,C_82),k1_zfmisc_1(A_80))
      | ~ m1_subset_1(C_82,k1_zfmisc_1(k2_zfmisc_1(A_80,B_81))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_212,plain,
    ( m1_subset_1(k1_relat_1('#skF_4'),k1_zfmisc_1('#skF_3'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_168,c_193])).

tff(c_220,plain,(
    m1_subset_1(k1_relat_1('#skF_4'),k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_212])).

tff(c_142,plain,(
    ! [A_69] :
      ( r2_hidden('#skF_2'(A_69),k1_relat_1(A_69))
      | v2_funct_1(A_69)
      | ~ v1_funct_1(A_69)
      | ~ v1_relat_1(A_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_2,plain,(
    ! [C_4,A_1,B_2] :
      ( r2_hidden(C_4,A_1)
      | ~ r2_hidden(C_4,B_2)
      | ~ m1_subset_1(B_2,k1_zfmisc_1(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_737,plain,(
    ! [A_138,A_139] :
      ( r2_hidden('#skF_2'(A_138),A_139)
      | ~ m1_subset_1(k1_relat_1(A_138),k1_zfmisc_1(A_139))
      | v2_funct_1(A_138)
      | ~ v1_funct_1(A_138)
      | ~ v1_relat_1(A_138) ) ),
    inference(resolution,[status(thm)],[c_142,c_2])).

tff(c_749,plain,
    ( r2_hidden('#skF_2'('#skF_4'),'#skF_3')
    | v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_220,c_737])).

tff(c_768,plain,
    ( r2_hidden('#skF_2'('#skF_4'),'#skF_3')
    | v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_36,c_749])).

tff(c_770,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_57,c_381,c_768])).

tff(c_772,plain,(
    r2_hidden('#skF_2'('#skF_4'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_289])).

tff(c_282,plain,(
    ! [D_38] :
      ( D_38 = '#skF_2'('#skF_4')
      | k1_funct_1('#skF_4',D_38) != k1_funct_1('#skF_4','#skF_1'('#skF_4'))
      | ~ r2_hidden(D_38,'#skF_3')
      | ~ r2_hidden('#skF_2'('#skF_4'),'#skF_3')
      | v2_funct_1('#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_273,c_99])).

tff(c_291,plain,(
    ! [D_38] :
      ( D_38 = '#skF_2'('#skF_4')
      | k1_funct_1('#skF_4',D_38) != k1_funct_1('#skF_4','#skF_1'('#skF_4'))
      | ~ r2_hidden(D_38,'#skF_3')
      | ~ r2_hidden('#skF_2'('#skF_4'),'#skF_3')
      | v2_funct_1('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_36,c_282])).

tff(c_292,plain,(
    ! [D_38] :
      ( D_38 = '#skF_2'('#skF_4')
      | k1_funct_1('#skF_4',D_38) != k1_funct_1('#skF_4','#skF_1'('#skF_4'))
      | ~ r2_hidden(D_38,'#skF_3')
      | ~ r2_hidden('#skF_2'('#skF_4'),'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_57,c_291])).

tff(c_804,plain,(
    ! [D_38] :
      ( D_38 = '#skF_2'('#skF_4')
      | k1_funct_1('#skF_4',D_38) != k1_funct_1('#skF_4','#skF_1'('#skF_4'))
      | ~ r2_hidden(D_38,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_772,c_292])).

tff(c_807,plain,
    ( '#skF_2'('#skF_4') = '#skF_1'('#skF_4')
    | ~ r2_hidden('#skF_1'('#skF_4'),'#skF_3') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_804])).

tff(c_808,plain,(
    ~ r2_hidden('#skF_1'('#skF_4'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_98,c_807])).

tff(c_131,plain,(
    ! [A_68] :
      ( r2_hidden('#skF_1'(A_68),k1_relat_1(A_68))
      | v2_funct_1(A_68)
      | ~ v1_funct_1(A_68)
      | ~ v1_relat_1(A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_1194,plain,(
    ! [A_181,A_182] :
      ( r2_hidden('#skF_1'(A_181),A_182)
      | ~ m1_subset_1(k1_relat_1(A_181),k1_zfmisc_1(A_182))
      | v2_funct_1(A_181)
      | ~ v1_funct_1(A_181)
      | ~ v1_relat_1(A_181) ) ),
    inference(resolution,[status(thm)],[c_131,c_2])).

tff(c_1203,plain,
    ( r2_hidden('#skF_1'('#skF_4'),'#skF_3')
    | v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_220,c_1194])).

tff(c_1219,plain,
    ( r2_hidden('#skF_1'('#skF_4'),'#skF_3')
    | v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_36,c_1203])).

tff(c_1221,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_57,c_808,c_1219])).

tff(c_1223,plain,(
    v2_funct_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_42,plain,
    ( r2_hidden('#skF_6','#skF_3')
    | ~ v2_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_1228,plain,(
    r2_hidden('#skF_6','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1223,c_42])).

tff(c_3207,plain,(
    ! [D_371,C_372,B_373,A_374] :
      ( k1_funct_1(k2_funct_1(D_371),k1_funct_1(D_371,C_372)) = C_372
      | k1_xboole_0 = B_373
      | ~ r2_hidden(C_372,A_374)
      | ~ v2_funct_1(D_371)
      | ~ m1_subset_1(D_371,k1_zfmisc_1(k2_zfmisc_1(A_374,B_373)))
      | ~ v1_funct_2(D_371,A_374,B_373)
      | ~ v1_funct_1(D_371) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_3250,plain,(
    ! [D_377,B_378] :
      ( k1_funct_1(k2_funct_1(D_377),k1_funct_1(D_377,'#skF_6')) = '#skF_6'
      | k1_xboole_0 = B_378
      | ~ v2_funct_1(D_377)
      | ~ m1_subset_1(D_377,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_378)))
      | ~ v1_funct_2(D_377,'#skF_3',B_378)
      | ~ v1_funct_1(D_377) ) ),
    inference(resolution,[status(thm)],[c_1228,c_3207])).

tff(c_3264,plain,
    ( k1_funct_1(k2_funct_1('#skF_4'),k1_funct_1('#skF_4','#skF_6')) = '#skF_6'
    | k1_xboole_0 = '#skF_3'
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_2('#skF_4','#skF_3','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_32,c_3250])).

tff(c_3274,plain,
    ( k1_funct_1(k2_funct_1('#skF_4'),k1_funct_1('#skF_4','#skF_6')) = '#skF_6'
    | k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_1223,c_3264])).

tff(c_3313,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_3274])).

tff(c_4,plain,(
    ! [A_5] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_5)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_1239,plain,(
    ! [A_188,B_189] :
      ( r1_tarski(A_188,B_189)
      | ~ m1_subset_1(A_188,k1_zfmisc_1(B_189)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_1251,plain,(
    ! [A_5] : r1_tarski(k1_xboole_0,A_5) ),
    inference(resolution,[status(thm)],[c_4,c_1239])).

tff(c_3333,plain,(
    ! [A_5] : r1_tarski('#skF_3',A_5) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3313,c_1251])).

tff(c_44,plain,
    ( r2_hidden('#skF_5','#skF_3')
    | ~ v2_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_1225,plain,(
    r2_hidden('#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1223,c_44])).

tff(c_1229,plain,(
    ! [B_184,A_185] :
      ( ~ r1_tarski(B_184,A_185)
      | ~ r2_hidden(A_185,B_184) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_1237,plain,(
    ~ r1_tarski('#skF_3','#skF_5') ),
    inference(resolution,[status(thm)],[c_1225,c_1229])).

tff(c_3363,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3333,c_1237])).

tff(c_3365,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_3274])).

tff(c_1222,plain,(
    '#skF_5' != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_3364,plain,(
    k1_funct_1(k2_funct_1('#skF_4'),k1_funct_1('#skF_4','#skF_6')) = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_3274])).

tff(c_40,plain,
    ( k1_funct_1('#skF_4','#skF_5') = k1_funct_1('#skF_4','#skF_6')
    | ~ v2_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_1254,plain,(
    k1_funct_1('#skF_4','#skF_5') = k1_funct_1('#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1223,c_40])).

tff(c_3405,plain,(
    ! [D_388,B_389] :
      ( k1_funct_1(k2_funct_1(D_388),k1_funct_1(D_388,'#skF_5')) = '#skF_5'
      | k1_xboole_0 = B_389
      | ~ v2_funct_1(D_388)
      | ~ m1_subset_1(D_388,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_389)))
      | ~ v1_funct_2(D_388,'#skF_3',B_389)
      | ~ v1_funct_1(D_388) ) ),
    inference(resolution,[status(thm)],[c_1225,c_3207])).

tff(c_3419,plain,
    ( k1_funct_1(k2_funct_1('#skF_4'),k1_funct_1('#skF_4','#skF_5')) = '#skF_5'
    | k1_xboole_0 = '#skF_3'
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_2('#skF_4','#skF_3','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_32,c_3405])).

tff(c_3429,plain,
    ( '#skF_5' = '#skF_6'
    | k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_1223,c_3364,c_1254,c_3419])).

tff(c_3431,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3365,c_1222,c_3429])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:07:29 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.37/2.15  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.52/2.15  
% 5.52/2.15  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.52/2.16  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4
% 5.52/2.16  
% 5.52/2.16  %Foreground sorts:
% 5.52/2.16  
% 5.52/2.16  
% 5.52/2.16  %Background operators:
% 5.52/2.16  
% 5.52/2.16  
% 5.52/2.16  %Foreground operators:
% 5.52/2.16  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.52/2.16  tff('#skF_2', type, '#skF_2': $i > $i).
% 5.52/2.16  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 5.52/2.16  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 5.52/2.16  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.52/2.16  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.52/2.16  tff('#skF_1', type, '#skF_1': $i > $i).
% 5.52/2.16  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.52/2.16  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.52/2.16  tff('#skF_5', type, '#skF_5': $i).
% 5.52/2.16  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.52/2.16  tff('#skF_6', type, '#skF_6': $i).
% 5.52/2.16  tff('#skF_3', type, '#skF_3': $i).
% 5.52/2.16  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 5.52/2.16  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.52/2.16  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 5.52/2.16  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.52/2.16  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.52/2.16  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.52/2.16  tff('#skF_4', type, '#skF_4': $i).
% 5.52/2.16  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.52/2.16  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.52/2.16  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.52/2.16  
% 5.52/2.17  tff(f_108, negated_conjecture, ~(![A, B]: (((v1_funct_1(B) & v1_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (v2_funct_1(B) <=> (![C, D]: (((r2_hidden(C, A) & r2_hidden(D, A)) & (k1_funct_1(B, C) = k1_funct_1(B, D))) => (C = D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_funct_2)).
% 5.52/2.17  tff(f_68, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 5.52/2.17  tff(f_59, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) <=> (![B, C]: (((r2_hidden(B, k1_relat_1(A)) & r2_hidden(C, k1_relat_1(A))) & (k1_funct_1(A, B) = k1_funct_1(A, C))) => (B = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_funct_1)).
% 5.52/2.17  tff(f_76, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 5.52/2.17  tff(f_72, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k1_relset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_relset_1)).
% 5.52/2.17  tff(f_32, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 5.52/2.17  tff(f_90, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(D) & r2_hidden(C, A)) => ((B = k1_xboole_0) | (k1_funct_1(k2_funct_1(D), k1_funct_1(D, C)) = C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t32_funct_2)).
% 5.52/2.17  tff(f_34, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 5.52/2.17  tff(f_38, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 5.52/2.17  tff(f_64, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 5.52/2.17  tff(c_36, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_108])).
% 5.52/2.17  tff(c_34, plain, (v1_funct_2('#skF_4', '#skF_3', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_108])).
% 5.52/2.17  tff(c_38, plain, ('#skF_5'!='#skF_6' | ~v2_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_108])).
% 5.52/2.17  tff(c_57, plain, (~v2_funct_1('#skF_4')), inference(splitLeft, [status(thm)], [c_38])).
% 5.52/2.17  tff(c_32, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_108])).
% 5.52/2.17  tff(c_75, plain, (![C_47, A_48, B_49]: (v1_relat_1(C_47) | ~m1_subset_1(C_47, k1_zfmisc_1(k2_zfmisc_1(A_48, B_49))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 5.52/2.17  tff(c_88, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_32, c_75])).
% 5.52/2.17  tff(c_90, plain, (![A_50]: ('#skF_2'(A_50)!='#skF_1'(A_50) | v2_funct_1(A_50) | ~v1_funct_1(A_50) | ~v1_relat_1(A_50))), inference(cnfTransformation, [status(thm)], [f_59])).
% 5.52/2.17  tff(c_93, plain, ('#skF_2'('#skF_4')!='#skF_1'('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_90, c_57])).
% 5.52/2.17  tff(c_96, plain, ('#skF_2'('#skF_4')!='#skF_1'('#skF_4') | ~v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_93])).
% 5.52/2.17  tff(c_98, plain, ('#skF_2'('#skF_4')!='#skF_1'('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_96])).
% 5.52/2.17  tff(c_273, plain, (![A_85]: (k1_funct_1(A_85, '#skF_2'(A_85))=k1_funct_1(A_85, '#skF_1'(A_85)) | v2_funct_1(A_85) | ~v1_funct_1(A_85) | ~v1_relat_1(A_85))), inference(cnfTransformation, [status(thm)], [f_59])).
% 5.52/2.17  tff(c_56, plain, (![D_38, C_37]: (v2_funct_1('#skF_4') | D_38=C_37 | k1_funct_1('#skF_4', D_38)!=k1_funct_1('#skF_4', C_37) | ~r2_hidden(D_38, '#skF_3') | ~r2_hidden(C_37, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_108])).
% 5.52/2.17  tff(c_99, plain, (![D_38, C_37]: (D_38=C_37 | k1_funct_1('#skF_4', D_38)!=k1_funct_1('#skF_4', C_37) | ~r2_hidden(D_38, '#skF_3') | ~r2_hidden(C_37, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_57, c_56])).
% 5.52/2.17  tff(c_279, plain, (![C_37]: (C_37='#skF_2'('#skF_4') | k1_funct_1('#skF_4', C_37)!=k1_funct_1('#skF_4', '#skF_1'('#skF_4')) | ~r2_hidden('#skF_2'('#skF_4'), '#skF_3') | ~r2_hidden(C_37, '#skF_3') | v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_273, c_99])).
% 5.52/2.17  tff(c_288, plain, (![C_37]: (C_37='#skF_2'('#skF_4') | k1_funct_1('#skF_4', C_37)!=k1_funct_1('#skF_4', '#skF_1'('#skF_4')) | ~r2_hidden('#skF_2'('#skF_4'), '#skF_3') | ~r2_hidden(C_37, '#skF_3') | v2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_36, c_279])).
% 5.52/2.17  tff(c_289, plain, (![C_37]: (C_37='#skF_2'('#skF_4') | k1_funct_1('#skF_4', C_37)!=k1_funct_1('#skF_4', '#skF_1'('#skF_4')) | ~r2_hidden('#skF_2'('#skF_4'), '#skF_3') | ~r2_hidden(C_37, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_57, c_288])).
% 5.52/2.17  tff(c_381, plain, (~r2_hidden('#skF_2'('#skF_4'), '#skF_3')), inference(splitLeft, [status(thm)], [c_289])).
% 5.52/2.17  tff(c_155, plain, (![A_72, B_73, C_74]: (k1_relset_1(A_72, B_73, C_74)=k1_relat_1(C_74) | ~m1_subset_1(C_74, k1_zfmisc_1(k2_zfmisc_1(A_72, B_73))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 5.52/2.17  tff(c_168, plain, (k1_relset_1('#skF_3', '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_32, c_155])).
% 5.52/2.17  tff(c_193, plain, (![A_80, B_81, C_82]: (m1_subset_1(k1_relset_1(A_80, B_81, C_82), k1_zfmisc_1(A_80)) | ~m1_subset_1(C_82, k1_zfmisc_1(k2_zfmisc_1(A_80, B_81))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 5.52/2.17  tff(c_212, plain, (m1_subset_1(k1_relat_1('#skF_4'), k1_zfmisc_1('#skF_3')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_168, c_193])).
% 5.52/2.17  tff(c_220, plain, (m1_subset_1(k1_relat_1('#skF_4'), k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_212])).
% 5.52/2.17  tff(c_142, plain, (![A_69]: (r2_hidden('#skF_2'(A_69), k1_relat_1(A_69)) | v2_funct_1(A_69) | ~v1_funct_1(A_69) | ~v1_relat_1(A_69))), inference(cnfTransformation, [status(thm)], [f_59])).
% 5.52/2.17  tff(c_2, plain, (![C_4, A_1, B_2]: (r2_hidden(C_4, A_1) | ~r2_hidden(C_4, B_2) | ~m1_subset_1(B_2, k1_zfmisc_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.52/2.17  tff(c_737, plain, (![A_138, A_139]: (r2_hidden('#skF_2'(A_138), A_139) | ~m1_subset_1(k1_relat_1(A_138), k1_zfmisc_1(A_139)) | v2_funct_1(A_138) | ~v1_funct_1(A_138) | ~v1_relat_1(A_138))), inference(resolution, [status(thm)], [c_142, c_2])).
% 5.52/2.17  tff(c_749, plain, (r2_hidden('#skF_2'('#skF_4'), '#skF_3') | v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_220, c_737])).
% 5.52/2.17  tff(c_768, plain, (r2_hidden('#skF_2'('#skF_4'), '#skF_3') | v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_36, c_749])).
% 5.52/2.17  tff(c_770, plain, $false, inference(negUnitSimplification, [status(thm)], [c_57, c_381, c_768])).
% 5.52/2.17  tff(c_772, plain, (r2_hidden('#skF_2'('#skF_4'), '#skF_3')), inference(splitRight, [status(thm)], [c_289])).
% 5.52/2.17  tff(c_282, plain, (![D_38]: (D_38='#skF_2'('#skF_4') | k1_funct_1('#skF_4', D_38)!=k1_funct_1('#skF_4', '#skF_1'('#skF_4')) | ~r2_hidden(D_38, '#skF_3') | ~r2_hidden('#skF_2'('#skF_4'), '#skF_3') | v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_273, c_99])).
% 5.52/2.17  tff(c_291, plain, (![D_38]: (D_38='#skF_2'('#skF_4') | k1_funct_1('#skF_4', D_38)!=k1_funct_1('#skF_4', '#skF_1'('#skF_4')) | ~r2_hidden(D_38, '#skF_3') | ~r2_hidden('#skF_2'('#skF_4'), '#skF_3') | v2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_36, c_282])).
% 5.52/2.17  tff(c_292, plain, (![D_38]: (D_38='#skF_2'('#skF_4') | k1_funct_1('#skF_4', D_38)!=k1_funct_1('#skF_4', '#skF_1'('#skF_4')) | ~r2_hidden(D_38, '#skF_3') | ~r2_hidden('#skF_2'('#skF_4'), '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_57, c_291])).
% 5.52/2.17  tff(c_804, plain, (![D_38]: (D_38='#skF_2'('#skF_4') | k1_funct_1('#skF_4', D_38)!=k1_funct_1('#skF_4', '#skF_1'('#skF_4')) | ~r2_hidden(D_38, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_772, c_292])).
% 5.52/2.17  tff(c_807, plain, ('#skF_2'('#skF_4')='#skF_1'('#skF_4') | ~r2_hidden('#skF_1'('#skF_4'), '#skF_3')), inference(reflexivity, [status(thm), theory('equality')], [c_804])).
% 5.52/2.17  tff(c_808, plain, (~r2_hidden('#skF_1'('#skF_4'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_98, c_807])).
% 5.52/2.17  tff(c_131, plain, (![A_68]: (r2_hidden('#skF_1'(A_68), k1_relat_1(A_68)) | v2_funct_1(A_68) | ~v1_funct_1(A_68) | ~v1_relat_1(A_68))), inference(cnfTransformation, [status(thm)], [f_59])).
% 5.52/2.17  tff(c_1194, plain, (![A_181, A_182]: (r2_hidden('#skF_1'(A_181), A_182) | ~m1_subset_1(k1_relat_1(A_181), k1_zfmisc_1(A_182)) | v2_funct_1(A_181) | ~v1_funct_1(A_181) | ~v1_relat_1(A_181))), inference(resolution, [status(thm)], [c_131, c_2])).
% 5.52/2.17  tff(c_1203, plain, (r2_hidden('#skF_1'('#skF_4'), '#skF_3') | v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_220, c_1194])).
% 5.52/2.17  tff(c_1219, plain, (r2_hidden('#skF_1'('#skF_4'), '#skF_3') | v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_36, c_1203])).
% 5.52/2.17  tff(c_1221, plain, $false, inference(negUnitSimplification, [status(thm)], [c_57, c_808, c_1219])).
% 5.52/2.17  tff(c_1223, plain, (v2_funct_1('#skF_4')), inference(splitRight, [status(thm)], [c_38])).
% 5.52/2.17  tff(c_42, plain, (r2_hidden('#skF_6', '#skF_3') | ~v2_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_108])).
% 5.52/2.17  tff(c_1228, plain, (r2_hidden('#skF_6', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1223, c_42])).
% 5.52/2.17  tff(c_3207, plain, (![D_371, C_372, B_373, A_374]: (k1_funct_1(k2_funct_1(D_371), k1_funct_1(D_371, C_372))=C_372 | k1_xboole_0=B_373 | ~r2_hidden(C_372, A_374) | ~v2_funct_1(D_371) | ~m1_subset_1(D_371, k1_zfmisc_1(k2_zfmisc_1(A_374, B_373))) | ~v1_funct_2(D_371, A_374, B_373) | ~v1_funct_1(D_371))), inference(cnfTransformation, [status(thm)], [f_90])).
% 5.52/2.17  tff(c_3250, plain, (![D_377, B_378]: (k1_funct_1(k2_funct_1(D_377), k1_funct_1(D_377, '#skF_6'))='#skF_6' | k1_xboole_0=B_378 | ~v2_funct_1(D_377) | ~m1_subset_1(D_377, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_378))) | ~v1_funct_2(D_377, '#skF_3', B_378) | ~v1_funct_1(D_377))), inference(resolution, [status(thm)], [c_1228, c_3207])).
% 5.52/2.17  tff(c_3264, plain, (k1_funct_1(k2_funct_1('#skF_4'), k1_funct_1('#skF_4', '#skF_6'))='#skF_6' | k1_xboole_0='#skF_3' | ~v2_funct_1('#skF_4') | ~v1_funct_2('#skF_4', '#skF_3', '#skF_3') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_32, c_3250])).
% 5.52/2.17  tff(c_3274, plain, (k1_funct_1(k2_funct_1('#skF_4'), k1_funct_1('#skF_4', '#skF_6'))='#skF_6' | k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_1223, c_3264])).
% 5.52/2.17  tff(c_3313, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_3274])).
% 5.52/2.17  tff(c_4, plain, (![A_5]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 5.52/2.17  tff(c_1239, plain, (![A_188, B_189]: (r1_tarski(A_188, B_189) | ~m1_subset_1(A_188, k1_zfmisc_1(B_189)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.52/2.17  tff(c_1251, plain, (![A_5]: (r1_tarski(k1_xboole_0, A_5))), inference(resolution, [status(thm)], [c_4, c_1239])).
% 5.52/2.17  tff(c_3333, plain, (![A_5]: (r1_tarski('#skF_3', A_5))), inference(demodulation, [status(thm), theory('equality')], [c_3313, c_1251])).
% 5.52/2.17  tff(c_44, plain, (r2_hidden('#skF_5', '#skF_3') | ~v2_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_108])).
% 5.52/2.17  tff(c_1225, plain, (r2_hidden('#skF_5', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1223, c_44])).
% 5.52/2.17  tff(c_1229, plain, (![B_184, A_185]: (~r1_tarski(B_184, A_185) | ~r2_hidden(A_185, B_184))), inference(cnfTransformation, [status(thm)], [f_64])).
% 5.52/2.17  tff(c_1237, plain, (~r1_tarski('#skF_3', '#skF_5')), inference(resolution, [status(thm)], [c_1225, c_1229])).
% 5.52/2.17  tff(c_3363, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3333, c_1237])).
% 5.52/2.17  tff(c_3365, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_3274])).
% 5.52/2.17  tff(c_1222, plain, ('#skF_5'!='#skF_6'), inference(splitRight, [status(thm)], [c_38])).
% 5.52/2.17  tff(c_3364, plain, (k1_funct_1(k2_funct_1('#skF_4'), k1_funct_1('#skF_4', '#skF_6'))='#skF_6'), inference(splitRight, [status(thm)], [c_3274])).
% 5.52/2.17  tff(c_40, plain, (k1_funct_1('#skF_4', '#skF_5')=k1_funct_1('#skF_4', '#skF_6') | ~v2_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_108])).
% 5.52/2.17  tff(c_1254, plain, (k1_funct_1('#skF_4', '#skF_5')=k1_funct_1('#skF_4', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_1223, c_40])).
% 5.52/2.17  tff(c_3405, plain, (![D_388, B_389]: (k1_funct_1(k2_funct_1(D_388), k1_funct_1(D_388, '#skF_5'))='#skF_5' | k1_xboole_0=B_389 | ~v2_funct_1(D_388) | ~m1_subset_1(D_388, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_389))) | ~v1_funct_2(D_388, '#skF_3', B_389) | ~v1_funct_1(D_388))), inference(resolution, [status(thm)], [c_1225, c_3207])).
% 5.52/2.17  tff(c_3419, plain, (k1_funct_1(k2_funct_1('#skF_4'), k1_funct_1('#skF_4', '#skF_5'))='#skF_5' | k1_xboole_0='#skF_3' | ~v2_funct_1('#skF_4') | ~v1_funct_2('#skF_4', '#skF_3', '#skF_3') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_32, c_3405])).
% 5.52/2.17  tff(c_3429, plain, ('#skF_5'='#skF_6' | k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_1223, c_3364, c_1254, c_3419])).
% 5.52/2.17  tff(c_3431, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3365, c_1222, c_3429])).
% 5.52/2.17  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.52/2.17  
% 5.52/2.17  Inference rules
% 5.52/2.17  ----------------------
% 5.52/2.17  #Ref     : 7
% 5.52/2.17  #Sup     : 669
% 5.52/2.17  #Fact    : 0
% 5.52/2.17  #Define  : 0
% 5.52/2.17  #Split   : 28
% 5.52/2.17  #Chain   : 0
% 5.52/2.17  #Close   : 0
% 5.52/2.17  
% 5.52/2.17  Ordering : KBO
% 5.52/2.17  
% 5.52/2.17  Simplification rules
% 5.52/2.17  ----------------------
% 5.52/2.17  #Subsume      : 127
% 5.52/2.17  #Demod        : 499
% 5.52/2.17  #Tautology    : 185
% 5.52/2.17  #SimpNegUnit  : 15
% 5.52/2.17  #BackRed      : 172
% 5.52/2.17  
% 5.52/2.17  #Partial instantiations: 0
% 5.52/2.17  #Strategies tried      : 1
% 5.52/2.17  
% 5.52/2.17  Timing (in seconds)
% 5.52/2.17  ----------------------
% 5.52/2.18  Preprocessing        : 0.38
% 5.52/2.18  Parsing              : 0.22
% 5.52/2.18  CNF conversion       : 0.02
% 5.52/2.18  Main loop            : 0.99
% 5.52/2.18  Inferencing          : 0.35
% 5.52/2.18  Reduction            : 0.34
% 5.52/2.18  Demodulation         : 0.23
% 5.52/2.18  BG Simplification    : 0.04
% 5.52/2.18  Subsumption          : 0.17
% 5.52/2.18  Abstraction          : 0.04
% 5.52/2.18  MUC search           : 0.00
% 5.52/2.18  Cooper               : 0.00
% 5.52/2.18  Total                : 1.41
% 5.52/2.18  Index Insertion      : 0.00
% 5.52/2.18  Index Deletion       : 0.00
% 5.52/2.18  Index Matching       : 0.00
% 5.52/2.18  BG Taut test         : 0.00
%------------------------------------------------------------------------------
