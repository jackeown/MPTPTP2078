%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:42 EST 2020

% Result     : Theorem 3.74s
% Output     : CNFRefutation 3.92s
% Verified   : 
% Statistics : Number of formulae       :  126 ( 422 expanded)
%              Number of leaves         :   33 ( 152 expanded)
%              Depth                    :   11
%              Number of atoms          :  267 (1392 expanded)
%              Number of equality atoms :   66 ( 331 expanded)
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

tff(f_107,negated_conjecture,(
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

tff(f_67,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_63,axiom,(
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

tff(f_75,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k1_relset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_relset_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_89,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( v2_funct_1(D)
          & r2_hidden(C,A) )
       => ( B = k1_xboole_0
          | k1_funct_1(k2_funct_1(D),k1_funct_1(D,C)) = C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_funct_2)).

tff(f_38,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_48,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(c_38,plain,
    ( '#skF_5' != '#skF_6'
    | ~ v2_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_57,plain,(
    ~ v2_funct_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_38])).

tff(c_32,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_81,plain,(
    ! [C_45,A_46,B_47] :
      ( v1_relat_1(C_45)
      | ~ m1_subset_1(C_45,k1_zfmisc_1(k2_zfmisc_1(A_46,B_47))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_94,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_32,c_81])).

tff(c_36,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_96,plain,(
    ! [A_48] :
      ( '#skF_2'(A_48) != '#skF_1'(A_48)
      | v2_funct_1(A_48)
      | ~ v1_funct_1(A_48)
      | ~ v1_relat_1(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_99,plain,
    ( '#skF_2'('#skF_4') != '#skF_1'('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_96,c_57])).

tff(c_102,plain,
    ( '#skF_2'('#skF_4') != '#skF_1'('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_99])).

tff(c_104,plain,(
    '#skF_2'('#skF_4') != '#skF_1'('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_102])).

tff(c_235,plain,(
    ! [A_80] :
      ( k1_funct_1(A_80,'#skF_2'(A_80)) = k1_funct_1(A_80,'#skF_1'(A_80))
      | v2_funct_1(A_80)
      | ~ v1_funct_1(A_80)
      | ~ v1_relat_1(A_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_56,plain,(
    ! [D_37,C_36] :
      ( v2_funct_1('#skF_4')
      | D_37 = C_36
      | k1_funct_1('#skF_4',D_37) != k1_funct_1('#skF_4',C_36)
      | ~ r2_hidden(D_37,'#skF_3')
      | ~ r2_hidden(C_36,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_105,plain,(
    ! [D_37,C_36] :
      ( D_37 = C_36
      | k1_funct_1('#skF_4',D_37) != k1_funct_1('#skF_4',C_36)
      | ~ r2_hidden(D_37,'#skF_3')
      | ~ r2_hidden(C_36,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_57,c_56])).

tff(c_244,plain,(
    ! [D_37] :
      ( D_37 = '#skF_2'('#skF_4')
      | k1_funct_1('#skF_4',D_37) != k1_funct_1('#skF_4','#skF_1'('#skF_4'))
      | ~ r2_hidden(D_37,'#skF_3')
      | ~ r2_hidden('#skF_2'('#skF_4'),'#skF_3')
      | v2_funct_1('#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_235,c_105])).

tff(c_253,plain,(
    ! [D_37] :
      ( D_37 = '#skF_2'('#skF_4')
      | k1_funct_1('#skF_4',D_37) != k1_funct_1('#skF_4','#skF_1'('#skF_4'))
      | ~ r2_hidden(D_37,'#skF_3')
      | ~ r2_hidden('#skF_2'('#skF_4'),'#skF_3')
      | v2_funct_1('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_36,c_244])).

tff(c_254,plain,(
    ! [D_37] :
      ( D_37 = '#skF_2'('#skF_4')
      | k1_funct_1('#skF_4',D_37) != k1_funct_1('#skF_4','#skF_1'('#skF_4'))
      | ~ r2_hidden(D_37,'#skF_3')
      | ~ r2_hidden('#skF_2'('#skF_4'),'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_57,c_253])).

tff(c_412,plain,(
    ~ r2_hidden('#skF_2'('#skF_4'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_254])).

tff(c_151,plain,(
    ! [A_68,B_69,C_70] :
      ( k1_relset_1(A_68,B_69,C_70) = k1_relat_1(C_70)
      | ~ m1_subset_1(C_70,k1_zfmisc_1(k2_zfmisc_1(A_68,B_69))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_164,plain,(
    k1_relset_1('#skF_3','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_32,c_151])).

tff(c_189,plain,(
    ! [A_76,B_77,C_78] :
      ( m1_subset_1(k1_relset_1(A_76,B_77,C_78),k1_zfmisc_1(A_76))
      | ~ m1_subset_1(C_78,k1_zfmisc_1(k2_zfmisc_1(A_76,B_77))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_208,plain,
    ( m1_subset_1(k1_relat_1('#skF_4'),k1_zfmisc_1('#skF_3'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_164,c_189])).

tff(c_216,plain,(
    m1_subset_1(k1_relat_1('#skF_4'),k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_208])).

tff(c_144,plain,(
    ! [A_67] :
      ( r2_hidden('#skF_2'(A_67),k1_relat_1(A_67))
      | v2_funct_1(A_67)
      | ~ v1_funct_1(A_67)
      | ~ v1_relat_1(A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_4,plain,(
    ! [C_5,A_2,B_3] :
      ( r2_hidden(C_5,A_2)
      | ~ r2_hidden(C_5,B_3)
      | ~ m1_subset_1(B_3,k1_zfmisc_1(A_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_447,plain,(
    ! [A_108,A_109] :
      ( r2_hidden('#skF_2'(A_108),A_109)
      | ~ m1_subset_1(k1_relat_1(A_108),k1_zfmisc_1(A_109))
      | v2_funct_1(A_108)
      | ~ v1_funct_1(A_108)
      | ~ v1_relat_1(A_108) ) ),
    inference(resolution,[status(thm)],[c_144,c_4])).

tff(c_450,plain,
    ( r2_hidden('#skF_2'('#skF_4'),'#skF_3')
    | v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_216,c_447])).

tff(c_460,plain,
    ( r2_hidden('#skF_2'('#skF_4'),'#skF_3')
    | v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_36,c_450])).

tff(c_462,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_57,c_412,c_460])).

tff(c_464,plain,(
    r2_hidden('#skF_2'('#skF_4'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_254])).

tff(c_241,plain,(
    ! [C_36] :
      ( C_36 = '#skF_2'('#skF_4')
      | k1_funct_1('#skF_4',C_36) != k1_funct_1('#skF_4','#skF_1'('#skF_4'))
      | ~ r2_hidden('#skF_2'('#skF_4'),'#skF_3')
      | ~ r2_hidden(C_36,'#skF_3')
      | v2_funct_1('#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_235,c_105])).

tff(c_250,plain,(
    ! [C_36] :
      ( C_36 = '#skF_2'('#skF_4')
      | k1_funct_1('#skF_4',C_36) != k1_funct_1('#skF_4','#skF_1'('#skF_4'))
      | ~ r2_hidden('#skF_2'('#skF_4'),'#skF_3')
      | ~ r2_hidden(C_36,'#skF_3')
      | v2_funct_1('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_36,c_241])).

tff(c_251,plain,(
    ! [C_36] :
      ( C_36 = '#skF_2'('#skF_4')
      | k1_funct_1('#skF_4',C_36) != k1_funct_1('#skF_4','#skF_1'('#skF_4'))
      | ~ r2_hidden('#skF_2'('#skF_4'),'#skF_3')
      | ~ r2_hidden(C_36,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_57,c_250])).

tff(c_526,plain,(
    ! [C_36] :
      ( C_36 = '#skF_2'('#skF_4')
      | k1_funct_1('#skF_4',C_36) != k1_funct_1('#skF_4','#skF_1'('#skF_4'))
      | ~ r2_hidden(C_36,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_464,c_251])).

tff(c_529,plain,
    ( '#skF_2'('#skF_4') = '#skF_1'('#skF_4')
    | ~ r2_hidden('#skF_1'('#skF_4'),'#skF_3') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_526])).

tff(c_530,plain,(
    ~ r2_hidden('#skF_1'('#skF_4'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_104,c_529])).

tff(c_136,plain,(
    ! [A_63] :
      ( r2_hidden('#skF_1'(A_63),k1_relat_1(A_63))
      | v2_funct_1(A_63)
      | ~ v1_funct_1(A_63)
      | ~ v1_relat_1(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_782,plain,(
    ! [A_152,A_153] :
      ( r2_hidden('#skF_1'(A_152),A_153)
      | ~ m1_subset_1(k1_relat_1(A_152),k1_zfmisc_1(A_153))
      | v2_funct_1(A_152)
      | ~ v1_funct_1(A_152)
      | ~ v1_relat_1(A_152) ) ),
    inference(resolution,[status(thm)],[c_136,c_4])).

tff(c_785,plain,
    ( r2_hidden('#skF_1'('#skF_4'),'#skF_3')
    | v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_216,c_782])).

tff(c_795,plain,
    ( r2_hidden('#skF_1'('#skF_4'),'#skF_3')
    | v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_36,c_785])).

tff(c_797,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_57,c_530,c_795])).

tff(c_798,plain,(
    '#skF_5' != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_34,plain,(
    v1_funct_2('#skF_4','#skF_3','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_799,plain,(
    v2_funct_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_42,plain,
    ( r2_hidden('#skF_6','#skF_3')
    | ~ v2_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_805,plain,(
    r2_hidden('#skF_6','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_799,c_42])).

tff(c_1211,plain,(
    ! [D_217,C_218,B_219,A_220] :
      ( k1_funct_1(k2_funct_1(D_217),k1_funct_1(D_217,C_218)) = C_218
      | k1_xboole_0 = B_219
      | ~ r2_hidden(C_218,A_220)
      | ~ v2_funct_1(D_217)
      | ~ m1_subset_1(D_217,k1_zfmisc_1(k2_zfmisc_1(A_220,B_219)))
      | ~ v1_funct_2(D_217,A_220,B_219)
      | ~ v1_funct_1(D_217) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_1260,plain,(
    ! [D_227,B_228] :
      ( k1_funct_1(k2_funct_1(D_227),k1_funct_1(D_227,'#skF_6')) = '#skF_6'
      | k1_xboole_0 = B_228
      | ~ v2_funct_1(D_227)
      | ~ m1_subset_1(D_227,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_228)))
      | ~ v1_funct_2(D_227,'#skF_3',B_228)
      | ~ v1_funct_1(D_227) ) ),
    inference(resolution,[status(thm)],[c_805,c_1211])).

tff(c_1268,plain,
    ( k1_funct_1(k2_funct_1('#skF_4'),k1_funct_1('#skF_4','#skF_6')) = '#skF_6'
    | k1_xboole_0 = '#skF_3'
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_2('#skF_4','#skF_3','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_32,c_1260])).

tff(c_1276,plain,
    ( k1_funct_1(k2_funct_1('#skF_4'),k1_funct_1('#skF_4','#skF_6')) = '#skF_6'
    | k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_799,c_1268])).

tff(c_1278,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_1276])).

tff(c_6,plain,(
    ! [A_6] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_6)) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_806,plain,(
    ! [A_156,B_157] :
      ( r1_tarski(A_156,B_157)
      | ~ m1_subset_1(A_156,k1_zfmisc_1(B_157)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_814,plain,(
    ! [A_6] : r1_tarski(k1_xboole_0,A_6) ),
    inference(resolution,[status(thm)],[c_6,c_806])).

tff(c_1287,plain,(
    ! [A_6] : r1_tarski('#skF_3',A_6) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1278,c_814])).

tff(c_10,plain,(
    ! [A_7,B_8] :
      ( m1_subset_1(A_7,k1_zfmisc_1(B_8))
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_44,plain,
    ( r2_hidden('#skF_5','#skF_3')
    | ~ v2_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_803,plain,(
    r2_hidden('#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_799,c_44])).

tff(c_848,plain,(
    ! [C_164,A_165,B_166] :
      ( r2_hidden(C_164,A_165)
      | ~ r2_hidden(C_164,B_166)
      | ~ m1_subset_1(B_166,k1_zfmisc_1(A_165)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_877,plain,(
    ! [A_172] :
      ( r2_hidden('#skF_5',A_172)
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_172)) ) ),
    inference(resolution,[status(thm)],[c_803,c_848])).

tff(c_882,plain,(
    ! [B_8] :
      ( r2_hidden('#skF_5',B_8)
      | ~ r1_tarski('#skF_3',B_8) ) ),
    inference(resolution,[status(thm)],[c_10,c_877])).

tff(c_983,plain,(
    ! [A_200,B_201,C_202] :
      ( k1_relset_1(A_200,B_201,C_202) = k1_relat_1(C_202)
      | ~ m1_subset_1(C_202,k1_zfmisc_1(k2_zfmisc_1(A_200,B_201))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_996,plain,(
    k1_relset_1('#skF_3','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_32,c_983])).

tff(c_26,plain,(
    ! [A_22,B_23,C_24] :
      ( m1_subset_1(k1_relset_1(A_22,B_23,C_24),k1_zfmisc_1(A_22))
      | ~ m1_subset_1(C_24,k1_zfmisc_1(k2_zfmisc_1(A_22,B_23))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_1027,plain,
    ( m1_subset_1(k1_relat_1('#skF_4'),k1_zfmisc_1('#skF_3'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_996,c_26])).

tff(c_1031,plain,(
    m1_subset_1(k1_relat_1('#skF_4'),k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_1027])).

tff(c_12,plain,(
    ! [A_9,C_11,B_10] :
      ( m1_subset_1(A_9,C_11)
      | ~ m1_subset_1(B_10,k1_zfmisc_1(C_11))
      | ~ r2_hidden(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_1156,plain,(
    ! [A_213] :
      ( m1_subset_1(A_213,'#skF_3')
      | ~ r2_hidden(A_213,k1_relat_1('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_1031,c_12])).

tff(c_1179,plain,
    ( m1_subset_1('#skF_5','#skF_3')
    | ~ r1_tarski('#skF_3',k1_relat_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_882,c_1156])).

tff(c_1182,plain,(
    ~ r1_tarski('#skF_3',k1_relat_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_1179])).

tff(c_1318,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1287,c_1182])).

tff(c_1320,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_1276])).

tff(c_1319,plain,(
    k1_funct_1(k2_funct_1('#skF_4'),k1_funct_1('#skF_4','#skF_6')) = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_1276])).

tff(c_40,plain,
    ( k1_funct_1('#skF_4','#skF_5') = k1_funct_1('#skF_4','#skF_6')
    | ~ v2_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_823,plain,(
    k1_funct_1('#skF_4','#skF_5') = k1_funct_1('#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_799,c_40])).

tff(c_1378,plain,(
    ! [D_234,B_235] :
      ( k1_funct_1(k2_funct_1(D_234),k1_funct_1(D_234,'#skF_5')) = '#skF_5'
      | k1_xboole_0 = B_235
      | ~ v2_funct_1(D_234)
      | ~ m1_subset_1(D_234,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_235)))
      | ~ v1_funct_2(D_234,'#skF_3',B_235)
      | ~ v1_funct_1(D_234) ) ),
    inference(resolution,[status(thm)],[c_803,c_1211])).

tff(c_1386,plain,
    ( k1_funct_1(k2_funct_1('#skF_4'),k1_funct_1('#skF_4','#skF_5')) = '#skF_5'
    | k1_xboole_0 = '#skF_3'
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_2('#skF_4','#skF_3','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_32,c_1378])).

tff(c_1394,plain,
    ( '#skF_5' = '#skF_6'
    | k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_799,c_1319,c_823,c_1386])).

tff(c_1396,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1320,c_798,c_1394])).

tff(c_1398,plain,(
    r1_tarski('#skF_3',k1_relat_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_1179])).

tff(c_867,plain,(
    ! [A_170] :
      ( r2_hidden('#skF_6',A_170)
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_170)) ) ),
    inference(resolution,[status(thm)],[c_805,c_848])).

tff(c_872,plain,(
    ! [B_8] :
      ( r2_hidden('#skF_6',B_8)
      | ~ r1_tarski('#skF_3',B_8) ) ),
    inference(resolution,[status(thm)],[c_10,c_867])).

tff(c_833,plain,(
    ! [C_161,A_162,B_163] :
      ( v1_relat_1(C_161)
      | ~ m1_subset_1(C_161,k1_zfmisc_1(k2_zfmisc_1(A_162,B_163))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_846,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_32,c_833])).

tff(c_1425,plain,(
    ! [C_236,B_237,A_238] :
      ( C_236 = B_237
      | k1_funct_1(A_238,C_236) != k1_funct_1(A_238,B_237)
      | ~ r2_hidden(C_236,k1_relat_1(A_238))
      | ~ r2_hidden(B_237,k1_relat_1(A_238))
      | ~ v2_funct_1(A_238)
      | ~ v1_funct_1(A_238)
      | ~ v1_relat_1(A_238) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_1433,plain,(
    ! [C_236] :
      ( C_236 = '#skF_5'
      | k1_funct_1('#skF_4',C_236) != k1_funct_1('#skF_4','#skF_6')
      | ~ r2_hidden(C_236,k1_relat_1('#skF_4'))
      | ~ r2_hidden('#skF_5',k1_relat_1('#skF_4'))
      | ~ v2_funct_1('#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_823,c_1425])).

tff(c_1437,plain,(
    ! [C_236] :
      ( C_236 = '#skF_5'
      | k1_funct_1('#skF_4',C_236) != k1_funct_1('#skF_4','#skF_6')
      | ~ r2_hidden(C_236,k1_relat_1('#skF_4'))
      | ~ r2_hidden('#skF_5',k1_relat_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_846,c_36,c_799,c_1433])).

tff(c_1442,plain,(
    ~ r2_hidden('#skF_5',k1_relat_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_1437])).

tff(c_1445,plain,(
    ~ r1_tarski('#skF_3',k1_relat_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_882,c_1442])).

tff(c_1449,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1398,c_1445])).

tff(c_1613,plain,(
    ! [C_254] :
      ( C_254 = '#skF_5'
      | k1_funct_1('#skF_4',C_254) != k1_funct_1('#skF_4','#skF_6')
      | ~ r2_hidden(C_254,k1_relat_1('#skF_4')) ) ),
    inference(splitRight,[status(thm)],[c_1437])).

tff(c_1632,plain,
    ( '#skF_5' = '#skF_6'
    | ~ r1_tarski('#skF_3',k1_relat_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_872,c_1613])).

tff(c_1649,plain,(
    '#skF_5' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1398,c_1632])).

tff(c_1651,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_798,c_1649])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 09:24:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.74/1.63  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.74/1.64  
% 3.74/1.64  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.74/1.64  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4
% 3.74/1.64  
% 3.74/1.64  %Foreground sorts:
% 3.74/1.64  
% 3.74/1.64  
% 3.74/1.64  %Background operators:
% 3.74/1.64  
% 3.74/1.64  
% 3.74/1.64  %Foreground operators:
% 3.74/1.64  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.74/1.64  tff('#skF_2', type, '#skF_2': $i > $i).
% 3.74/1.64  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 3.74/1.64  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 3.74/1.64  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.74/1.64  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.74/1.64  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.74/1.64  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.74/1.64  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.74/1.64  tff('#skF_5', type, '#skF_5': $i).
% 3.74/1.64  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.74/1.64  tff('#skF_6', type, '#skF_6': $i).
% 3.74/1.64  tff('#skF_3', type, '#skF_3': $i).
% 3.74/1.64  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.74/1.64  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.74/1.64  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.74/1.64  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.74/1.64  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.74/1.64  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.74/1.64  tff('#skF_4', type, '#skF_4': $i).
% 3.74/1.64  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.74/1.64  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.74/1.64  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.74/1.64  
% 3.92/1.66  tff(f_107, negated_conjecture, ~(![A, B]: (((v1_funct_1(B) & v1_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (v2_funct_1(B) <=> (![C, D]: (((r2_hidden(C, A) & r2_hidden(D, A)) & (k1_funct_1(B, C) = k1_funct_1(B, D))) => (C = D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_funct_2)).
% 3.92/1.66  tff(f_67, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.92/1.66  tff(f_63, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) <=> (![B, C]: (((r2_hidden(B, k1_relat_1(A)) & r2_hidden(C, k1_relat_1(A))) & (k1_funct_1(A, B) = k1_funct_1(A, C))) => (B = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_funct_1)).
% 3.92/1.66  tff(f_75, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.92/1.66  tff(f_71, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k1_relset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_relset_1)).
% 3.92/1.66  tff(f_36, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 3.92/1.66  tff(f_89, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(D) & r2_hidden(C, A)) => ((B = k1_xboole_0) | (k1_funct_1(k2_funct_1(D), k1_funct_1(D, C)) = C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t32_funct_2)).
% 3.92/1.66  tff(f_38, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 3.92/1.66  tff(f_42, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 3.92/1.66  tff(f_48, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 3.92/1.66  tff(c_38, plain, ('#skF_5'!='#skF_6' | ~v2_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.92/1.66  tff(c_57, plain, (~v2_funct_1('#skF_4')), inference(splitLeft, [status(thm)], [c_38])).
% 3.92/1.66  tff(c_32, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.92/1.66  tff(c_81, plain, (![C_45, A_46, B_47]: (v1_relat_1(C_45) | ~m1_subset_1(C_45, k1_zfmisc_1(k2_zfmisc_1(A_46, B_47))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.92/1.66  tff(c_94, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_32, c_81])).
% 3.92/1.66  tff(c_36, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.92/1.66  tff(c_96, plain, (![A_48]: ('#skF_2'(A_48)!='#skF_1'(A_48) | v2_funct_1(A_48) | ~v1_funct_1(A_48) | ~v1_relat_1(A_48))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.92/1.66  tff(c_99, plain, ('#skF_2'('#skF_4')!='#skF_1'('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_96, c_57])).
% 3.92/1.66  tff(c_102, plain, ('#skF_2'('#skF_4')!='#skF_1'('#skF_4') | ~v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_99])).
% 3.92/1.66  tff(c_104, plain, ('#skF_2'('#skF_4')!='#skF_1'('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_94, c_102])).
% 3.92/1.66  tff(c_235, plain, (![A_80]: (k1_funct_1(A_80, '#skF_2'(A_80))=k1_funct_1(A_80, '#skF_1'(A_80)) | v2_funct_1(A_80) | ~v1_funct_1(A_80) | ~v1_relat_1(A_80))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.92/1.66  tff(c_56, plain, (![D_37, C_36]: (v2_funct_1('#skF_4') | D_37=C_36 | k1_funct_1('#skF_4', D_37)!=k1_funct_1('#skF_4', C_36) | ~r2_hidden(D_37, '#skF_3') | ~r2_hidden(C_36, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.92/1.66  tff(c_105, plain, (![D_37, C_36]: (D_37=C_36 | k1_funct_1('#skF_4', D_37)!=k1_funct_1('#skF_4', C_36) | ~r2_hidden(D_37, '#skF_3') | ~r2_hidden(C_36, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_57, c_56])).
% 3.92/1.66  tff(c_244, plain, (![D_37]: (D_37='#skF_2'('#skF_4') | k1_funct_1('#skF_4', D_37)!=k1_funct_1('#skF_4', '#skF_1'('#skF_4')) | ~r2_hidden(D_37, '#skF_3') | ~r2_hidden('#skF_2'('#skF_4'), '#skF_3') | v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_235, c_105])).
% 3.92/1.66  tff(c_253, plain, (![D_37]: (D_37='#skF_2'('#skF_4') | k1_funct_1('#skF_4', D_37)!=k1_funct_1('#skF_4', '#skF_1'('#skF_4')) | ~r2_hidden(D_37, '#skF_3') | ~r2_hidden('#skF_2'('#skF_4'), '#skF_3') | v2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_36, c_244])).
% 3.92/1.66  tff(c_254, plain, (![D_37]: (D_37='#skF_2'('#skF_4') | k1_funct_1('#skF_4', D_37)!=k1_funct_1('#skF_4', '#skF_1'('#skF_4')) | ~r2_hidden(D_37, '#skF_3') | ~r2_hidden('#skF_2'('#skF_4'), '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_57, c_253])).
% 3.92/1.66  tff(c_412, plain, (~r2_hidden('#skF_2'('#skF_4'), '#skF_3')), inference(splitLeft, [status(thm)], [c_254])).
% 3.92/1.66  tff(c_151, plain, (![A_68, B_69, C_70]: (k1_relset_1(A_68, B_69, C_70)=k1_relat_1(C_70) | ~m1_subset_1(C_70, k1_zfmisc_1(k2_zfmisc_1(A_68, B_69))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.92/1.66  tff(c_164, plain, (k1_relset_1('#skF_3', '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_32, c_151])).
% 3.92/1.66  tff(c_189, plain, (![A_76, B_77, C_78]: (m1_subset_1(k1_relset_1(A_76, B_77, C_78), k1_zfmisc_1(A_76)) | ~m1_subset_1(C_78, k1_zfmisc_1(k2_zfmisc_1(A_76, B_77))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.92/1.66  tff(c_208, plain, (m1_subset_1(k1_relat_1('#skF_4'), k1_zfmisc_1('#skF_3')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_164, c_189])).
% 3.92/1.66  tff(c_216, plain, (m1_subset_1(k1_relat_1('#skF_4'), k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_208])).
% 3.92/1.66  tff(c_144, plain, (![A_67]: (r2_hidden('#skF_2'(A_67), k1_relat_1(A_67)) | v2_funct_1(A_67) | ~v1_funct_1(A_67) | ~v1_relat_1(A_67))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.92/1.66  tff(c_4, plain, (![C_5, A_2, B_3]: (r2_hidden(C_5, A_2) | ~r2_hidden(C_5, B_3) | ~m1_subset_1(B_3, k1_zfmisc_1(A_2)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.92/1.66  tff(c_447, plain, (![A_108, A_109]: (r2_hidden('#skF_2'(A_108), A_109) | ~m1_subset_1(k1_relat_1(A_108), k1_zfmisc_1(A_109)) | v2_funct_1(A_108) | ~v1_funct_1(A_108) | ~v1_relat_1(A_108))), inference(resolution, [status(thm)], [c_144, c_4])).
% 3.92/1.66  tff(c_450, plain, (r2_hidden('#skF_2'('#skF_4'), '#skF_3') | v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_216, c_447])).
% 3.92/1.66  tff(c_460, plain, (r2_hidden('#skF_2'('#skF_4'), '#skF_3') | v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_94, c_36, c_450])).
% 3.92/1.66  tff(c_462, plain, $false, inference(negUnitSimplification, [status(thm)], [c_57, c_412, c_460])).
% 3.92/1.66  tff(c_464, plain, (r2_hidden('#skF_2'('#skF_4'), '#skF_3')), inference(splitRight, [status(thm)], [c_254])).
% 3.92/1.66  tff(c_241, plain, (![C_36]: (C_36='#skF_2'('#skF_4') | k1_funct_1('#skF_4', C_36)!=k1_funct_1('#skF_4', '#skF_1'('#skF_4')) | ~r2_hidden('#skF_2'('#skF_4'), '#skF_3') | ~r2_hidden(C_36, '#skF_3') | v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_235, c_105])).
% 3.92/1.66  tff(c_250, plain, (![C_36]: (C_36='#skF_2'('#skF_4') | k1_funct_1('#skF_4', C_36)!=k1_funct_1('#skF_4', '#skF_1'('#skF_4')) | ~r2_hidden('#skF_2'('#skF_4'), '#skF_3') | ~r2_hidden(C_36, '#skF_3') | v2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_36, c_241])).
% 3.92/1.66  tff(c_251, plain, (![C_36]: (C_36='#skF_2'('#skF_4') | k1_funct_1('#skF_4', C_36)!=k1_funct_1('#skF_4', '#skF_1'('#skF_4')) | ~r2_hidden('#skF_2'('#skF_4'), '#skF_3') | ~r2_hidden(C_36, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_57, c_250])).
% 3.92/1.66  tff(c_526, plain, (![C_36]: (C_36='#skF_2'('#skF_4') | k1_funct_1('#skF_4', C_36)!=k1_funct_1('#skF_4', '#skF_1'('#skF_4')) | ~r2_hidden(C_36, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_464, c_251])).
% 3.92/1.66  tff(c_529, plain, ('#skF_2'('#skF_4')='#skF_1'('#skF_4') | ~r2_hidden('#skF_1'('#skF_4'), '#skF_3')), inference(reflexivity, [status(thm), theory('equality')], [c_526])).
% 3.92/1.66  tff(c_530, plain, (~r2_hidden('#skF_1'('#skF_4'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_104, c_529])).
% 3.92/1.66  tff(c_136, plain, (![A_63]: (r2_hidden('#skF_1'(A_63), k1_relat_1(A_63)) | v2_funct_1(A_63) | ~v1_funct_1(A_63) | ~v1_relat_1(A_63))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.92/1.66  tff(c_782, plain, (![A_152, A_153]: (r2_hidden('#skF_1'(A_152), A_153) | ~m1_subset_1(k1_relat_1(A_152), k1_zfmisc_1(A_153)) | v2_funct_1(A_152) | ~v1_funct_1(A_152) | ~v1_relat_1(A_152))), inference(resolution, [status(thm)], [c_136, c_4])).
% 3.92/1.66  tff(c_785, plain, (r2_hidden('#skF_1'('#skF_4'), '#skF_3') | v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_216, c_782])).
% 3.92/1.66  tff(c_795, plain, (r2_hidden('#skF_1'('#skF_4'), '#skF_3') | v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_94, c_36, c_785])).
% 3.92/1.66  tff(c_797, plain, $false, inference(negUnitSimplification, [status(thm)], [c_57, c_530, c_795])).
% 3.92/1.66  tff(c_798, plain, ('#skF_5'!='#skF_6'), inference(splitRight, [status(thm)], [c_38])).
% 3.92/1.66  tff(c_34, plain, (v1_funct_2('#skF_4', '#skF_3', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.92/1.66  tff(c_799, plain, (v2_funct_1('#skF_4')), inference(splitRight, [status(thm)], [c_38])).
% 3.92/1.66  tff(c_42, plain, (r2_hidden('#skF_6', '#skF_3') | ~v2_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.92/1.66  tff(c_805, plain, (r2_hidden('#skF_6', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_799, c_42])).
% 3.92/1.66  tff(c_1211, plain, (![D_217, C_218, B_219, A_220]: (k1_funct_1(k2_funct_1(D_217), k1_funct_1(D_217, C_218))=C_218 | k1_xboole_0=B_219 | ~r2_hidden(C_218, A_220) | ~v2_funct_1(D_217) | ~m1_subset_1(D_217, k1_zfmisc_1(k2_zfmisc_1(A_220, B_219))) | ~v1_funct_2(D_217, A_220, B_219) | ~v1_funct_1(D_217))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.92/1.66  tff(c_1260, plain, (![D_227, B_228]: (k1_funct_1(k2_funct_1(D_227), k1_funct_1(D_227, '#skF_6'))='#skF_6' | k1_xboole_0=B_228 | ~v2_funct_1(D_227) | ~m1_subset_1(D_227, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_228))) | ~v1_funct_2(D_227, '#skF_3', B_228) | ~v1_funct_1(D_227))), inference(resolution, [status(thm)], [c_805, c_1211])).
% 3.92/1.66  tff(c_1268, plain, (k1_funct_1(k2_funct_1('#skF_4'), k1_funct_1('#skF_4', '#skF_6'))='#skF_6' | k1_xboole_0='#skF_3' | ~v2_funct_1('#skF_4') | ~v1_funct_2('#skF_4', '#skF_3', '#skF_3') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_32, c_1260])).
% 3.92/1.66  tff(c_1276, plain, (k1_funct_1(k2_funct_1('#skF_4'), k1_funct_1('#skF_4', '#skF_6'))='#skF_6' | k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_799, c_1268])).
% 3.92/1.66  tff(c_1278, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_1276])).
% 3.92/1.66  tff(c_6, plain, (![A_6]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.92/1.66  tff(c_806, plain, (![A_156, B_157]: (r1_tarski(A_156, B_157) | ~m1_subset_1(A_156, k1_zfmisc_1(B_157)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.92/1.66  tff(c_814, plain, (![A_6]: (r1_tarski(k1_xboole_0, A_6))), inference(resolution, [status(thm)], [c_6, c_806])).
% 3.92/1.66  tff(c_1287, plain, (![A_6]: (r1_tarski('#skF_3', A_6))), inference(demodulation, [status(thm), theory('equality')], [c_1278, c_814])).
% 3.92/1.66  tff(c_10, plain, (![A_7, B_8]: (m1_subset_1(A_7, k1_zfmisc_1(B_8)) | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.92/1.66  tff(c_44, plain, (r2_hidden('#skF_5', '#skF_3') | ~v2_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.92/1.66  tff(c_803, plain, (r2_hidden('#skF_5', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_799, c_44])).
% 3.92/1.66  tff(c_848, plain, (![C_164, A_165, B_166]: (r2_hidden(C_164, A_165) | ~r2_hidden(C_164, B_166) | ~m1_subset_1(B_166, k1_zfmisc_1(A_165)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.92/1.66  tff(c_877, plain, (![A_172]: (r2_hidden('#skF_5', A_172) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_172)))), inference(resolution, [status(thm)], [c_803, c_848])).
% 3.92/1.66  tff(c_882, plain, (![B_8]: (r2_hidden('#skF_5', B_8) | ~r1_tarski('#skF_3', B_8))), inference(resolution, [status(thm)], [c_10, c_877])).
% 3.92/1.66  tff(c_983, plain, (![A_200, B_201, C_202]: (k1_relset_1(A_200, B_201, C_202)=k1_relat_1(C_202) | ~m1_subset_1(C_202, k1_zfmisc_1(k2_zfmisc_1(A_200, B_201))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.92/1.66  tff(c_996, plain, (k1_relset_1('#skF_3', '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_32, c_983])).
% 3.92/1.66  tff(c_26, plain, (![A_22, B_23, C_24]: (m1_subset_1(k1_relset_1(A_22, B_23, C_24), k1_zfmisc_1(A_22)) | ~m1_subset_1(C_24, k1_zfmisc_1(k2_zfmisc_1(A_22, B_23))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.92/1.66  tff(c_1027, plain, (m1_subset_1(k1_relat_1('#skF_4'), k1_zfmisc_1('#skF_3')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_996, c_26])).
% 3.92/1.66  tff(c_1031, plain, (m1_subset_1(k1_relat_1('#skF_4'), k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_1027])).
% 3.92/1.66  tff(c_12, plain, (![A_9, C_11, B_10]: (m1_subset_1(A_9, C_11) | ~m1_subset_1(B_10, k1_zfmisc_1(C_11)) | ~r2_hidden(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.92/1.66  tff(c_1156, plain, (![A_213]: (m1_subset_1(A_213, '#skF_3') | ~r2_hidden(A_213, k1_relat_1('#skF_4')))), inference(resolution, [status(thm)], [c_1031, c_12])).
% 3.92/1.66  tff(c_1179, plain, (m1_subset_1('#skF_5', '#skF_3') | ~r1_tarski('#skF_3', k1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_882, c_1156])).
% 3.92/1.66  tff(c_1182, plain, (~r1_tarski('#skF_3', k1_relat_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_1179])).
% 3.92/1.66  tff(c_1318, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1287, c_1182])).
% 3.92/1.66  tff(c_1320, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_1276])).
% 3.92/1.66  tff(c_1319, plain, (k1_funct_1(k2_funct_1('#skF_4'), k1_funct_1('#skF_4', '#skF_6'))='#skF_6'), inference(splitRight, [status(thm)], [c_1276])).
% 3.92/1.66  tff(c_40, plain, (k1_funct_1('#skF_4', '#skF_5')=k1_funct_1('#skF_4', '#skF_6') | ~v2_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.92/1.66  tff(c_823, plain, (k1_funct_1('#skF_4', '#skF_5')=k1_funct_1('#skF_4', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_799, c_40])).
% 3.92/1.66  tff(c_1378, plain, (![D_234, B_235]: (k1_funct_1(k2_funct_1(D_234), k1_funct_1(D_234, '#skF_5'))='#skF_5' | k1_xboole_0=B_235 | ~v2_funct_1(D_234) | ~m1_subset_1(D_234, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_235))) | ~v1_funct_2(D_234, '#skF_3', B_235) | ~v1_funct_1(D_234))), inference(resolution, [status(thm)], [c_803, c_1211])).
% 3.92/1.66  tff(c_1386, plain, (k1_funct_1(k2_funct_1('#skF_4'), k1_funct_1('#skF_4', '#skF_5'))='#skF_5' | k1_xboole_0='#skF_3' | ~v2_funct_1('#skF_4') | ~v1_funct_2('#skF_4', '#skF_3', '#skF_3') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_32, c_1378])).
% 3.92/1.66  tff(c_1394, plain, ('#skF_5'='#skF_6' | k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_799, c_1319, c_823, c_1386])).
% 3.92/1.66  tff(c_1396, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1320, c_798, c_1394])).
% 3.92/1.66  tff(c_1398, plain, (r1_tarski('#skF_3', k1_relat_1('#skF_4'))), inference(splitRight, [status(thm)], [c_1179])).
% 3.92/1.66  tff(c_867, plain, (![A_170]: (r2_hidden('#skF_6', A_170) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_170)))), inference(resolution, [status(thm)], [c_805, c_848])).
% 3.92/1.66  tff(c_872, plain, (![B_8]: (r2_hidden('#skF_6', B_8) | ~r1_tarski('#skF_3', B_8))), inference(resolution, [status(thm)], [c_10, c_867])).
% 3.92/1.66  tff(c_833, plain, (![C_161, A_162, B_163]: (v1_relat_1(C_161) | ~m1_subset_1(C_161, k1_zfmisc_1(k2_zfmisc_1(A_162, B_163))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.92/1.66  tff(c_846, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_32, c_833])).
% 3.92/1.66  tff(c_1425, plain, (![C_236, B_237, A_238]: (C_236=B_237 | k1_funct_1(A_238, C_236)!=k1_funct_1(A_238, B_237) | ~r2_hidden(C_236, k1_relat_1(A_238)) | ~r2_hidden(B_237, k1_relat_1(A_238)) | ~v2_funct_1(A_238) | ~v1_funct_1(A_238) | ~v1_relat_1(A_238))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.92/1.66  tff(c_1433, plain, (![C_236]: (C_236='#skF_5' | k1_funct_1('#skF_4', C_236)!=k1_funct_1('#skF_4', '#skF_6') | ~r2_hidden(C_236, k1_relat_1('#skF_4')) | ~r2_hidden('#skF_5', k1_relat_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_823, c_1425])).
% 3.92/1.66  tff(c_1437, plain, (![C_236]: (C_236='#skF_5' | k1_funct_1('#skF_4', C_236)!=k1_funct_1('#skF_4', '#skF_6') | ~r2_hidden(C_236, k1_relat_1('#skF_4')) | ~r2_hidden('#skF_5', k1_relat_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_846, c_36, c_799, c_1433])).
% 3.92/1.66  tff(c_1442, plain, (~r2_hidden('#skF_5', k1_relat_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_1437])).
% 3.92/1.66  tff(c_1445, plain, (~r1_tarski('#skF_3', k1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_882, c_1442])).
% 3.92/1.66  tff(c_1449, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1398, c_1445])).
% 3.92/1.66  tff(c_1613, plain, (![C_254]: (C_254='#skF_5' | k1_funct_1('#skF_4', C_254)!=k1_funct_1('#skF_4', '#skF_6') | ~r2_hidden(C_254, k1_relat_1('#skF_4')))), inference(splitRight, [status(thm)], [c_1437])).
% 3.92/1.66  tff(c_1632, plain, ('#skF_5'='#skF_6' | ~r1_tarski('#skF_3', k1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_872, c_1613])).
% 3.92/1.66  tff(c_1649, plain, ('#skF_5'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_1398, c_1632])).
% 3.92/1.66  tff(c_1651, plain, $false, inference(negUnitSimplification, [status(thm)], [c_798, c_1649])).
% 3.92/1.66  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.92/1.66  
% 3.92/1.66  Inference rules
% 3.92/1.66  ----------------------
% 3.92/1.66  #Ref     : 5
% 3.92/1.66  #Sup     : 318
% 3.92/1.66  #Fact    : 0
% 3.92/1.66  #Define  : 0
% 3.92/1.66  #Split   : 18
% 3.92/1.66  #Chain   : 0
% 3.92/1.66  #Close   : 0
% 3.92/1.66  
% 3.92/1.66  Ordering : KBO
% 3.92/1.66  
% 3.92/1.66  Simplification rules
% 3.92/1.66  ----------------------
% 3.92/1.66  #Subsume      : 65
% 3.92/1.66  #Demod        : 262
% 3.92/1.66  #Tautology    : 111
% 3.92/1.66  #SimpNegUnit  : 15
% 3.92/1.66  #BackRed      : 54
% 3.92/1.66  
% 3.92/1.66  #Partial instantiations: 0
% 3.92/1.66  #Strategies tried      : 1
% 3.92/1.66  
% 3.92/1.66  Timing (in seconds)
% 3.92/1.66  ----------------------
% 3.92/1.67  Preprocessing        : 0.31
% 3.92/1.67  Parsing              : 0.16
% 3.92/1.67  CNF conversion       : 0.02
% 3.92/1.67  Main loop            : 0.52
% 3.92/1.67  Inferencing          : 0.19
% 3.92/1.67  Reduction            : 0.17
% 3.92/1.67  Demodulation         : 0.11
% 3.92/1.67  BG Simplification    : 0.03
% 3.92/1.67  Subsumption          : 0.09
% 3.92/1.67  Abstraction          : 0.02
% 3.92/1.67  MUC search           : 0.00
% 3.92/1.67  Cooper               : 0.00
% 3.92/1.67  Total                : 0.88
% 3.92/1.67  Index Insertion      : 0.00
% 3.92/1.67  Index Deletion       : 0.00
% 3.92/1.67  Index Matching       : 0.00
% 3.92/1.67  BG Taut test         : 0.00
%------------------------------------------------------------------------------
