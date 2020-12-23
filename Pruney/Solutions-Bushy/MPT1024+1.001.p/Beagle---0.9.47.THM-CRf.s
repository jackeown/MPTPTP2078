%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1024+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:16 EST 2020

% Result     : Theorem 3.21s
% Output     : CNFRefutation 3.42s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 138 expanded)
%              Number of leaves         :   34 (  64 expanded)
%              Depth                    :   12
%              Number of atoms          :  127 ( 338 expanded)
%              Number of equality atoms :   19 (  50 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k1_relset_1 > k9_relat_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_9 > #skF_4 > #skF_8 > #skF_3

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

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_95,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [E] :
            ~ ( r2_hidden(E,k7_relset_1(A,B,D,C))
              & ! [F] :
                  ~ ( r2_hidden(F,A)
                    & r2_hidden(F,C)
                    & E = k1_funct_1(D,F) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t115_funct_2)).

tff(f_28,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_45,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B,C] :
          ( C = k9_relat_1(A,B)
        <=> ! [D] :
              ( r2_hidden(D,C)
            <=> ? [E] :
                  ( r2_hidden(E,k1_relat_1(A))
                  & r2_hidden(E,B)
                  & D = k1_funct_1(A,E) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_funct_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k1_relset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_relset_1)).

tff(f_69,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_76,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_63,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_57,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(c_44,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_50,plain,(
    ! [C_71,A_72,B_73] :
      ( v1_relat_1(C_71)
      | ~ m1_subset_1(C_71,k1_zfmisc_1(k2_zfmisc_1(A_72,B_73))) ) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_54,plain,(
    v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_44,c_50])).

tff(c_48,plain,(
    v1_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_921,plain,(
    ! [A_261,B_262,D_263] :
      ( r2_hidden('#skF_4'(A_261,B_262,k9_relat_1(A_261,B_262),D_263),k1_relat_1(A_261))
      | ~ r2_hidden(D_263,k9_relat_1(A_261,B_262))
      | ~ v1_funct_1(A_261)
      | ~ v1_relat_1(A_261) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_6,plain,(
    ! [A_4,B_27,D_42] :
      ( k1_funct_1(A_4,'#skF_4'(A_4,B_27,k9_relat_1(A_4,B_27),D_42)) = D_42
      | ~ r2_hidden(D_42,k9_relat_1(A_4,B_27))
      | ~ v1_funct_1(A_4)
      | ~ v1_relat_1(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_205,plain,(
    ! [A_117,B_118,D_119] :
      ( r2_hidden('#skF_4'(A_117,B_118,k9_relat_1(A_117,B_118),D_119),k1_relat_1(A_117))
      | ~ r2_hidden(D_119,k9_relat_1(A_117,B_118))
      | ~ v1_funct_1(A_117)
      | ~ v1_relat_1(A_117) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_71,plain,(
    ! [A_82,B_83,C_84] :
      ( k1_relset_1(A_82,B_83,C_84) = k1_relat_1(C_84)
      | ~ m1_subset_1(C_84,k1_zfmisc_1(k2_zfmisc_1(A_82,B_83))) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_75,plain,(
    k1_relset_1('#skF_5','#skF_6','#skF_8') = k1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_44,c_71])).

tff(c_80,plain,(
    ! [A_85,B_86,C_87] :
      ( m1_subset_1(k1_relset_1(A_85,B_86,C_87),k1_zfmisc_1(A_85))
      | ~ m1_subset_1(C_87,k1_zfmisc_1(k2_zfmisc_1(A_85,B_86))) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_95,plain,
    ( m1_subset_1(k1_relat_1('#skF_8'),k1_zfmisc_1('#skF_5'))
    | ~ m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_75,c_80])).

tff(c_101,plain,(
    m1_subset_1(k1_relat_1('#skF_8'),k1_zfmisc_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_95])).

tff(c_36,plain,(
    ! [A_58,C_60,B_59] :
      ( m1_subset_1(A_58,C_60)
      | ~ m1_subset_1(B_59,k1_zfmisc_1(C_60))
      | ~ r2_hidden(A_58,B_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_106,plain,(
    ! [A_58] :
      ( m1_subset_1(A_58,'#skF_5')
      | ~ r2_hidden(A_58,k1_relat_1('#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_101,c_36])).

tff(c_209,plain,(
    ! [B_118,D_119] :
      ( m1_subset_1('#skF_4'('#skF_8',B_118,k9_relat_1('#skF_8',B_118),D_119),'#skF_5')
      | ~ r2_hidden(D_119,k9_relat_1('#skF_8',B_118))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_205,c_106])).

tff(c_212,plain,(
    ! [B_118,D_119] :
      ( m1_subset_1('#skF_4'('#skF_8',B_118,k9_relat_1('#skF_8',B_118),D_119),'#skF_5')
      | ~ r2_hidden(D_119,k9_relat_1('#skF_8',B_118)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_48,c_209])).

tff(c_38,plain,(
    ! [C_63,B_62,A_61] :
      ( ~ v1_xboole_0(C_63)
      | ~ m1_subset_1(B_62,k1_zfmisc_1(C_63))
      | ~ r2_hidden(A_61,B_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_107,plain,(
    ! [A_61] :
      ( ~ v1_xboole_0('#skF_5')
      | ~ r2_hidden(A_61,k1_relat_1('#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_101,c_38])).

tff(c_108,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_107])).

tff(c_34,plain,(
    ! [A_56,B_57] :
      ( r2_hidden(A_56,B_57)
      | v1_xboole_0(B_57)
      | ~ m1_subset_1(A_56,B_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_169,plain,(
    ! [A_111,B_112,D_113] :
      ( r2_hidden('#skF_4'(A_111,B_112,k9_relat_1(A_111,B_112),D_113),B_112)
      | ~ r2_hidden(D_113,k9_relat_1(A_111,B_112))
      | ~ v1_funct_1(A_111)
      | ~ v1_relat_1(A_111) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_40,plain,(
    ! [F_68] :
      ( k1_funct_1('#skF_8',F_68) != '#skF_9'
      | ~ r2_hidden(F_68,'#skF_7')
      | ~ r2_hidden(F_68,'#skF_5') ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_597,plain,(
    ! [A_192,D_193] :
      ( k1_funct_1('#skF_8','#skF_4'(A_192,'#skF_7',k9_relat_1(A_192,'#skF_7'),D_193)) != '#skF_9'
      | ~ r2_hidden('#skF_4'(A_192,'#skF_7',k9_relat_1(A_192,'#skF_7'),D_193),'#skF_5')
      | ~ r2_hidden(D_193,k9_relat_1(A_192,'#skF_7'))
      | ~ v1_funct_1(A_192)
      | ~ v1_relat_1(A_192) ) ),
    inference(resolution,[status(thm)],[c_169,c_40])).

tff(c_600,plain,(
    ! [A_192,D_193] :
      ( k1_funct_1('#skF_8','#skF_4'(A_192,'#skF_7',k9_relat_1(A_192,'#skF_7'),D_193)) != '#skF_9'
      | ~ r2_hidden(D_193,k9_relat_1(A_192,'#skF_7'))
      | ~ v1_funct_1(A_192)
      | ~ v1_relat_1(A_192)
      | v1_xboole_0('#skF_5')
      | ~ m1_subset_1('#skF_4'(A_192,'#skF_7',k9_relat_1(A_192,'#skF_7'),D_193),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_34,c_597])).

tff(c_767,plain,(
    ! [A_220,D_221] :
      ( k1_funct_1('#skF_8','#skF_4'(A_220,'#skF_7',k9_relat_1(A_220,'#skF_7'),D_221)) != '#skF_9'
      | ~ r2_hidden(D_221,k9_relat_1(A_220,'#skF_7'))
      | ~ v1_funct_1(A_220)
      | ~ v1_relat_1(A_220)
      | ~ m1_subset_1('#skF_4'(A_220,'#skF_7',k9_relat_1(A_220,'#skF_7'),D_221),'#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_108,c_600])).

tff(c_771,plain,(
    ! [D_119] :
      ( k1_funct_1('#skF_8','#skF_4'('#skF_8','#skF_7',k9_relat_1('#skF_8','#skF_7'),D_119)) != '#skF_9'
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8')
      | ~ r2_hidden(D_119,k9_relat_1('#skF_8','#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_212,c_767])).

tff(c_775,plain,(
    ! [D_222] :
      ( k1_funct_1('#skF_8','#skF_4'('#skF_8','#skF_7',k9_relat_1('#skF_8','#skF_7'),D_222)) != '#skF_9'
      | ~ r2_hidden(D_222,k9_relat_1('#skF_8','#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_48,c_771])).

tff(c_779,plain,(
    ! [D_42] :
      ( D_42 != '#skF_9'
      | ~ r2_hidden(D_42,k9_relat_1('#skF_8','#skF_7'))
      | ~ r2_hidden(D_42,k9_relat_1('#skF_8','#skF_7'))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_775])).

tff(c_782,plain,(
    ~ r2_hidden('#skF_9',k9_relat_1('#skF_8','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_48,c_779])).

tff(c_126,plain,(
    ! [A_91,B_92,C_93,D_94] :
      ( k7_relset_1(A_91,B_92,C_93,D_94) = k9_relat_1(C_93,D_94)
      | ~ m1_subset_1(C_93,k1_zfmisc_1(k2_zfmisc_1(A_91,B_92))) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_133,plain,(
    ! [D_94] : k7_relset_1('#skF_5','#skF_6','#skF_8',D_94) = k9_relat_1('#skF_8',D_94) ),
    inference(resolution,[status(thm)],[c_44,c_126])).

tff(c_42,plain,(
    r2_hidden('#skF_9',k7_relset_1('#skF_5','#skF_6','#skF_8','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_134,plain,(
    r2_hidden('#skF_9',k9_relat_1('#skF_8','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_133,c_42])).

tff(c_784,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_782,c_134])).

tff(c_785,plain,(
    ! [A_61] : ~ r2_hidden(A_61,k1_relat_1('#skF_8')) ),
    inference(splitRight,[status(thm)],[c_107])).

tff(c_925,plain,(
    ! [D_263,B_262] :
      ( ~ r2_hidden(D_263,k9_relat_1('#skF_8',B_262))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_921,c_785])).

tff(c_928,plain,(
    ! [D_263,B_262] : ~ r2_hidden(D_263,k9_relat_1('#skF_8',B_262)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_48,c_925])).

tff(c_787,plain,(
    ! [A_223,B_224,C_225,D_226] :
      ( k7_relset_1(A_223,B_224,C_225,D_226) = k9_relat_1(C_225,D_226)
      | ~ m1_subset_1(C_225,k1_zfmisc_1(k2_zfmisc_1(A_223,B_224))) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_794,plain,(
    ! [D_226] : k7_relset_1('#skF_5','#skF_6','#skF_8',D_226) = k9_relat_1('#skF_8',D_226) ),
    inference(resolution,[status(thm)],[c_44,c_787])).

tff(c_802,plain,(
    r2_hidden('#skF_9',k9_relat_1('#skF_8','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_794,c_42])).

tff(c_936,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_928,c_802])).

%------------------------------------------------------------------------------
