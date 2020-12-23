%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:41 EST 2020

% Result     : Theorem 3.30s
% Output     : CNFRefutation 3.55s
% Verified   : 
% Statistics : Number of formulae       :  118 ( 372 expanded)
%              Number of leaves         :   33 ( 138 expanded)
%              Depth                    :   15
%              Number of atoms          :  250 (1237 expanded)
%              Number of equality atoms :   57 ( 287 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_7 > #skF_5 > #skF_6 > #skF_4 > #skF_3 > #skF_1

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

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

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_97,negated_conjecture,(
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

tff(f_59,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_55,axiom,(
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

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_79,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( v2_funct_1(D)
          & r2_hidden(C,A) )
       => ( B = k1_xboole_0
          | k1_funct_1(k2_funct_1(D),k1_funct_1(D,C)) = C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_funct_2)).

tff(f_34,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(c_32,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_59,plain,(
    ! [C_33,A_34,B_35] :
      ( v1_relat_1(C_33)
      | ~ m1_subset_1(C_33,k1_zfmisc_1(k2_zfmisc_1(A_34,B_35))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_63,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_32,c_59])).

tff(c_72,plain,(
    ! [C_41,A_42,B_43] :
      ( v4_relat_1(C_41,A_42)
      | ~ m1_subset_1(C_41,k1_zfmisc_1(k2_zfmisc_1(A_42,B_43))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_76,plain,(
    v4_relat_1('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_32,c_72])).

tff(c_12,plain,(
    ! [B_8,A_7] :
      ( r1_tarski(k1_relat_1(B_8),A_7)
      | ~ v4_relat_1(B_8,A_7)
      | ~ v1_relat_1(B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_38,plain,
    ( '#skF_7' != '#skF_6'
    | ~ v2_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_58,plain,(
    ~ v2_funct_1('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_38])).

tff(c_36,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_115,plain,(
    ! [A_59] :
      ( r2_hidden('#skF_3'(A_59),k1_relat_1(A_59))
      | v2_funct_1(A_59)
      | ~ v1_funct_1(A_59)
      | ~ v1_relat_1(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_118,plain,(
    ! [A_59,B_2] :
      ( r2_hidden('#skF_3'(A_59),B_2)
      | ~ r1_tarski(k1_relat_1(A_59),B_2)
      | v2_funct_1(A_59)
      | ~ v1_funct_1(A_59)
      | ~ v1_relat_1(A_59) ) ),
    inference(resolution,[status(thm)],[c_115,c_2])).

tff(c_104,plain,(
    ! [A_57] :
      ( '#skF_2'(A_57) != '#skF_3'(A_57)
      | v2_funct_1(A_57)
      | ~ v1_funct_1(A_57)
      | ~ v1_relat_1(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_107,plain,
    ( '#skF_2'('#skF_5') != '#skF_3'('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_104,c_58])).

tff(c_110,plain,(
    '#skF_2'('#skF_5') != '#skF_3'('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_36,c_107])).

tff(c_111,plain,(
    ! [A_58] :
      ( r2_hidden('#skF_2'(A_58),k1_relat_1(A_58))
      | v2_funct_1(A_58)
      | ~ v1_funct_1(A_58)
      | ~ v1_relat_1(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_114,plain,(
    ! [A_58,B_2] :
      ( r2_hidden('#skF_2'(A_58),B_2)
      | ~ r1_tarski(k1_relat_1(A_58),B_2)
      | v2_funct_1(A_58)
      | ~ v1_funct_1(A_58)
      | ~ v1_relat_1(A_58) ) ),
    inference(resolution,[status(thm)],[c_111,c_2])).

tff(c_128,plain,(
    ! [A_63] :
      ( k1_funct_1(A_63,'#skF_2'(A_63)) = k1_funct_1(A_63,'#skF_3'(A_63))
      | v2_funct_1(A_63)
      | ~ v1_funct_1(A_63)
      | ~ v1_relat_1(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_56,plain,(
    ! [D_31,C_30] :
      ( v2_funct_1('#skF_5')
      | D_31 = C_30
      | k1_funct_1('#skF_5',D_31) != k1_funct_1('#skF_5',C_30)
      | ~ r2_hidden(D_31,'#skF_4')
      | ~ r2_hidden(C_30,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_86,plain,(
    ! [D_31,C_30] :
      ( D_31 = C_30
      | k1_funct_1('#skF_5',D_31) != k1_funct_1('#skF_5',C_30)
      | ~ r2_hidden(D_31,'#skF_4')
      | ~ r2_hidden(C_30,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_56])).

tff(c_137,plain,(
    ! [D_31] :
      ( D_31 = '#skF_2'('#skF_5')
      | k1_funct_1('#skF_5',D_31) != k1_funct_1('#skF_5','#skF_3'('#skF_5'))
      | ~ r2_hidden(D_31,'#skF_4')
      | ~ r2_hidden('#skF_2'('#skF_5'),'#skF_4')
      | v2_funct_1('#skF_5')
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_128,c_86])).

tff(c_146,plain,(
    ! [D_31] :
      ( D_31 = '#skF_2'('#skF_5')
      | k1_funct_1('#skF_5',D_31) != k1_funct_1('#skF_5','#skF_3'('#skF_5'))
      | ~ r2_hidden(D_31,'#skF_4')
      | ~ r2_hidden('#skF_2'('#skF_5'),'#skF_4')
      | v2_funct_1('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_36,c_137])).

tff(c_147,plain,(
    ! [D_31] :
      ( D_31 = '#skF_2'('#skF_5')
      | k1_funct_1('#skF_5',D_31) != k1_funct_1('#skF_5','#skF_3'('#skF_5'))
      | ~ r2_hidden(D_31,'#skF_4')
      | ~ r2_hidden('#skF_2'('#skF_5'),'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_146])).

tff(c_204,plain,(
    ~ r2_hidden('#skF_2'('#skF_5'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_147])).

tff(c_207,plain,
    ( ~ r1_tarski(k1_relat_1('#skF_5'),'#skF_4')
    | v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_114,c_204])).

tff(c_210,plain,
    ( ~ r1_tarski(k1_relat_1('#skF_5'),'#skF_4')
    | v2_funct_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_36,c_207])).

tff(c_211,plain,(
    ~ r1_tarski(k1_relat_1('#skF_5'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_210])).

tff(c_217,plain,
    ( ~ v4_relat_1('#skF_5','#skF_4')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_12,c_211])).

tff(c_224,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_76,c_217])).

tff(c_226,plain,(
    r2_hidden('#skF_2'('#skF_5'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_147])).

tff(c_134,plain,(
    ! [C_30] :
      ( C_30 = '#skF_2'('#skF_5')
      | k1_funct_1('#skF_5',C_30) != k1_funct_1('#skF_5','#skF_3'('#skF_5'))
      | ~ r2_hidden('#skF_2'('#skF_5'),'#skF_4')
      | ~ r2_hidden(C_30,'#skF_4')
      | v2_funct_1('#skF_5')
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_128,c_86])).

tff(c_143,plain,(
    ! [C_30] :
      ( C_30 = '#skF_2'('#skF_5')
      | k1_funct_1('#skF_5',C_30) != k1_funct_1('#skF_5','#skF_3'('#skF_5'))
      | ~ r2_hidden('#skF_2'('#skF_5'),'#skF_4')
      | ~ r2_hidden(C_30,'#skF_4')
      | v2_funct_1('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_36,c_134])).

tff(c_144,plain,(
    ! [C_30] :
      ( C_30 = '#skF_2'('#skF_5')
      | k1_funct_1('#skF_5',C_30) != k1_funct_1('#skF_5','#skF_3'('#skF_5'))
      | ~ r2_hidden('#skF_2'('#skF_5'),'#skF_4')
      | ~ r2_hidden(C_30,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_143])).

tff(c_258,plain,(
    ! [C_30] :
      ( C_30 = '#skF_2'('#skF_5')
      | k1_funct_1('#skF_5',C_30) != k1_funct_1('#skF_5','#skF_3'('#skF_5'))
      | ~ r2_hidden(C_30,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_226,c_144])).

tff(c_261,plain,
    ( '#skF_2'('#skF_5') = '#skF_3'('#skF_5')
    | ~ r2_hidden('#skF_3'('#skF_5'),'#skF_4') ),
    inference(reflexivity,[status(thm),theory(equality)],[c_258])).

tff(c_262,plain,(
    ~ r2_hidden('#skF_3'('#skF_5'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_110,c_261])).

tff(c_274,plain,
    ( ~ r1_tarski(k1_relat_1('#skF_5'),'#skF_4')
    | v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_118,c_262])).

tff(c_277,plain,
    ( ~ r1_tarski(k1_relat_1('#skF_5'),'#skF_4')
    | v2_funct_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_36,c_274])).

tff(c_278,plain,(
    ~ r1_tarski(k1_relat_1('#skF_5'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_277])).

tff(c_284,plain,
    ( ~ v4_relat_1('#skF_5','#skF_4')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_12,c_278])).

tff(c_291,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_76,c_284])).

tff(c_292,plain,(
    '#skF_7' != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_310,plain,(
    ! [A_93,B_94] :
      ( ~ r2_hidden('#skF_1'(A_93,B_94),B_94)
      | r1_tarski(A_93,B_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_315,plain,(
    ! [A_1] : r1_tarski(A_1,A_1) ),
    inference(resolution,[status(thm)],[c_6,c_310])).

tff(c_34,plain,(
    v1_funct_2('#skF_5','#skF_4','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_293,plain,(
    v2_funct_1('#skF_5') ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_40,plain,
    ( k1_funct_1('#skF_5','#skF_7') = k1_funct_1('#skF_5','#skF_6')
    | ~ v2_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_304,plain,(
    k1_funct_1('#skF_5','#skF_7') = k1_funct_1('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_293,c_40])).

tff(c_42,plain,
    ( r2_hidden('#skF_7','#skF_4')
    | ~ v2_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_297,plain,(
    r2_hidden('#skF_7','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_293,c_42])).

tff(c_605,plain,(
    ! [D_178,C_179,B_180,A_181] :
      ( k1_funct_1(k2_funct_1(D_178),k1_funct_1(D_178,C_179)) = C_179
      | k1_xboole_0 = B_180
      | ~ r2_hidden(C_179,A_181)
      | ~ v2_funct_1(D_178)
      | ~ m1_subset_1(D_178,k1_zfmisc_1(k2_zfmisc_1(A_181,B_180)))
      | ~ v1_funct_2(D_178,A_181,B_180)
      | ~ v1_funct_1(D_178) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_668,plain,(
    ! [D_187,B_188] :
      ( k1_funct_1(k2_funct_1(D_187),k1_funct_1(D_187,'#skF_7')) = '#skF_7'
      | k1_xboole_0 = B_188
      | ~ v2_funct_1(D_187)
      | ~ m1_subset_1(D_187,k1_zfmisc_1(k2_zfmisc_1('#skF_4',B_188)))
      | ~ v1_funct_2(D_187,'#skF_4',B_188)
      | ~ v1_funct_1(D_187) ) ),
    inference(resolution,[status(thm)],[c_297,c_605])).

tff(c_670,plain,
    ( k1_funct_1(k2_funct_1('#skF_5'),k1_funct_1('#skF_5','#skF_7')) = '#skF_7'
    | k1_xboole_0 = '#skF_4'
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_2('#skF_5','#skF_4','#skF_4')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_32,c_668])).

tff(c_673,plain,
    ( k1_funct_1(k2_funct_1('#skF_5'),k1_funct_1('#skF_5','#skF_6')) = '#skF_7'
    | k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_293,c_304,c_670])).

tff(c_674,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_673])).

tff(c_8,plain,(
    ! [A_6] : r1_tarski(k1_xboole_0,A_6) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_44,plain,
    ( r2_hidden('#skF_6','#skF_4')
    | ~ v2_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_295,plain,(
    r2_hidden('#skF_6','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_293,c_44])).

tff(c_327,plain,(
    ! [C_102,B_103,A_104] :
      ( r2_hidden(C_102,B_103)
      | ~ r2_hidden(C_102,A_104)
      | ~ r1_tarski(A_104,B_103) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_342,plain,(
    ! [B_106] :
      ( r2_hidden('#skF_6',B_106)
      | ~ r1_tarski('#skF_4',B_106) ) ),
    inference(resolution,[status(thm)],[c_295,c_327])).

tff(c_359,plain,(
    ! [B_113,B_114] :
      ( r2_hidden('#skF_6',B_113)
      | ~ r1_tarski(B_114,B_113)
      | ~ r1_tarski('#skF_4',B_114) ) ),
    inference(resolution,[status(thm)],[c_342,c_2])).

tff(c_368,plain,(
    ! [A_6] :
      ( r2_hidden('#skF_6',A_6)
      | ~ r1_tarski('#skF_4',k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_8,c_359])).

tff(c_369,plain,(
    ~ r1_tarski('#skF_4',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_368])).

tff(c_685,plain,(
    ~ r1_tarski('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_674,c_369])).

tff(c_689,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_315,c_685])).

tff(c_691,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_673])).

tff(c_690,plain,(
    k1_funct_1(k2_funct_1('#skF_5'),k1_funct_1('#skF_5','#skF_6')) = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_673])).

tff(c_709,plain,(
    ! [D_192,B_193] :
      ( k1_funct_1(k2_funct_1(D_192),k1_funct_1(D_192,'#skF_6')) = '#skF_6'
      | k1_xboole_0 = B_193
      | ~ v2_funct_1(D_192)
      | ~ m1_subset_1(D_192,k1_zfmisc_1(k2_zfmisc_1('#skF_4',B_193)))
      | ~ v1_funct_2(D_192,'#skF_4',B_193)
      | ~ v1_funct_1(D_192) ) ),
    inference(resolution,[status(thm)],[c_295,c_605])).

tff(c_711,plain,
    ( k1_funct_1(k2_funct_1('#skF_5'),k1_funct_1('#skF_5','#skF_6')) = '#skF_6'
    | k1_xboole_0 = '#skF_4'
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_2('#skF_5','#skF_4','#skF_4')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_32,c_709])).

tff(c_714,plain,
    ( '#skF_7' = '#skF_6'
    | k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_293,c_690,c_711])).

tff(c_716,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_691,c_292,c_714])).

tff(c_717,plain,(
    ! [A_6] : r2_hidden('#skF_6',A_6) ),
    inference(splitRight,[status(thm)],[c_368])).

tff(c_298,plain,(
    ! [C_88,A_89,B_90] :
      ( v1_relat_1(C_88)
      | ~ m1_subset_1(C_88,k1_zfmisc_1(k2_zfmisc_1(A_89,B_90))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_302,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_32,c_298])).

tff(c_718,plain,(
    r1_tarski('#skF_4',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_368])).

tff(c_338,plain,(
    ! [B_105] :
      ( r2_hidden('#skF_7',B_105)
      | ~ r1_tarski('#skF_4',B_105) ) ),
    inference(resolution,[status(thm)],[c_297,c_327])).

tff(c_727,plain,(
    ! [B_195,B_196] :
      ( r2_hidden('#skF_7',B_195)
      | ~ r1_tarski(B_196,B_195)
      | ~ r1_tarski('#skF_4',B_196) ) ),
    inference(resolution,[status(thm)],[c_338,c_2])).

tff(c_735,plain,(
    ! [A_6] :
      ( r2_hidden('#skF_7',A_6)
      | ~ r1_tarski('#skF_4',k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_8,c_727])).

tff(c_743,plain,(
    ! [A_6] : r2_hidden('#skF_7',A_6) ),
    inference(demodulation,[status(thm),theory(equality)],[c_718,c_735])).

tff(c_927,plain,(
    ! [C_231,B_232,A_233] :
      ( C_231 = B_232
      | k1_funct_1(A_233,C_231) != k1_funct_1(A_233,B_232)
      | ~ r2_hidden(C_231,k1_relat_1(A_233))
      | ~ r2_hidden(B_232,k1_relat_1(A_233))
      | ~ v2_funct_1(A_233)
      | ~ v1_funct_1(A_233)
      | ~ v1_relat_1(A_233) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_933,plain,(
    ! [B_232] :
      ( B_232 = '#skF_7'
      | k1_funct_1('#skF_5',B_232) != k1_funct_1('#skF_5','#skF_6')
      | ~ r2_hidden('#skF_7',k1_relat_1('#skF_5'))
      | ~ r2_hidden(B_232,k1_relat_1('#skF_5'))
      | ~ v2_funct_1('#skF_5')
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_304,c_927])).

tff(c_975,plain,(
    ! [B_237] :
      ( B_237 = '#skF_7'
      | k1_funct_1('#skF_5',B_237) != k1_funct_1('#skF_5','#skF_6')
      | ~ r2_hidden(B_237,k1_relat_1('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_302,c_36,c_293,c_743,c_933])).

tff(c_1003,plain,(
    '#skF_7' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_717,c_975])).

tff(c_1024,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_292,c_1003])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n003.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 16:28:57 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.30/1.51  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.30/1.52  
% 3.30/1.52  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.30/1.52  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_7 > #skF_5 > #skF_6 > #skF_4 > #skF_3 > #skF_1
% 3.30/1.52  
% 3.30/1.52  %Foreground sorts:
% 3.30/1.52  
% 3.30/1.52  
% 3.30/1.52  %Background operators:
% 3.30/1.52  
% 3.30/1.52  
% 3.30/1.52  %Foreground operators:
% 3.30/1.52  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.30/1.52  tff('#skF_2', type, '#skF_2': $i > $i).
% 3.30/1.52  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 3.30/1.52  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 3.30/1.52  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.30/1.52  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.30/1.52  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.30/1.52  tff('#skF_7', type, '#skF_7': $i).
% 3.30/1.52  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.30/1.52  tff('#skF_5', type, '#skF_5': $i).
% 3.30/1.52  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.30/1.52  tff('#skF_6', type, '#skF_6': $i).
% 3.30/1.52  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.30/1.52  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.30/1.52  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.30/1.52  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.30/1.52  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.30/1.52  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.30/1.52  tff('#skF_4', type, '#skF_4': $i).
% 3.30/1.52  tff('#skF_3', type, '#skF_3': $i > $i).
% 3.30/1.52  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.30/1.52  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.30/1.52  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.30/1.52  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.30/1.52  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.30/1.52  
% 3.55/1.54  tff(f_97, negated_conjecture, ~(![A, B]: (((v1_funct_1(B) & v1_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (v2_funct_1(B) <=> (![C, D]: (((r2_hidden(C, A) & r2_hidden(D, A)) & (k1_funct_1(B, C) = k1_funct_1(B, D))) => (C = D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_funct_2)).
% 3.55/1.54  tff(f_59, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.55/1.54  tff(f_65, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.55/1.54  tff(f_40, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 3.55/1.54  tff(f_55, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) <=> (![B, C]: (((r2_hidden(B, k1_relat_1(A)) & r2_hidden(C, k1_relat_1(A))) & (k1_funct_1(A, B) = k1_funct_1(A, C))) => (B = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_funct_1)).
% 3.55/1.54  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 3.55/1.54  tff(f_79, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(D) & r2_hidden(C, A)) => ((B = k1_xboole_0) | (k1_funct_1(k2_funct_1(D), k1_funct_1(D, C)) = C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t32_funct_2)).
% 3.55/1.54  tff(f_34, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.55/1.54  tff(c_32, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.55/1.54  tff(c_59, plain, (![C_33, A_34, B_35]: (v1_relat_1(C_33) | ~m1_subset_1(C_33, k1_zfmisc_1(k2_zfmisc_1(A_34, B_35))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.55/1.54  tff(c_63, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_32, c_59])).
% 3.55/1.54  tff(c_72, plain, (![C_41, A_42, B_43]: (v4_relat_1(C_41, A_42) | ~m1_subset_1(C_41, k1_zfmisc_1(k2_zfmisc_1(A_42, B_43))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.55/1.54  tff(c_76, plain, (v4_relat_1('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_32, c_72])).
% 3.55/1.54  tff(c_12, plain, (![B_8, A_7]: (r1_tarski(k1_relat_1(B_8), A_7) | ~v4_relat_1(B_8, A_7) | ~v1_relat_1(B_8))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.55/1.54  tff(c_38, plain, ('#skF_7'!='#skF_6' | ~v2_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.55/1.54  tff(c_58, plain, (~v2_funct_1('#skF_5')), inference(splitLeft, [status(thm)], [c_38])).
% 3.55/1.54  tff(c_36, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.55/1.54  tff(c_115, plain, (![A_59]: (r2_hidden('#skF_3'(A_59), k1_relat_1(A_59)) | v2_funct_1(A_59) | ~v1_funct_1(A_59) | ~v1_relat_1(A_59))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.55/1.54  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.55/1.54  tff(c_118, plain, (![A_59, B_2]: (r2_hidden('#skF_3'(A_59), B_2) | ~r1_tarski(k1_relat_1(A_59), B_2) | v2_funct_1(A_59) | ~v1_funct_1(A_59) | ~v1_relat_1(A_59))), inference(resolution, [status(thm)], [c_115, c_2])).
% 3.55/1.54  tff(c_104, plain, (![A_57]: ('#skF_2'(A_57)!='#skF_3'(A_57) | v2_funct_1(A_57) | ~v1_funct_1(A_57) | ~v1_relat_1(A_57))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.55/1.54  tff(c_107, plain, ('#skF_2'('#skF_5')!='#skF_3'('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_104, c_58])).
% 3.55/1.54  tff(c_110, plain, ('#skF_2'('#skF_5')!='#skF_3'('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_63, c_36, c_107])).
% 3.55/1.54  tff(c_111, plain, (![A_58]: (r2_hidden('#skF_2'(A_58), k1_relat_1(A_58)) | v2_funct_1(A_58) | ~v1_funct_1(A_58) | ~v1_relat_1(A_58))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.55/1.54  tff(c_114, plain, (![A_58, B_2]: (r2_hidden('#skF_2'(A_58), B_2) | ~r1_tarski(k1_relat_1(A_58), B_2) | v2_funct_1(A_58) | ~v1_funct_1(A_58) | ~v1_relat_1(A_58))), inference(resolution, [status(thm)], [c_111, c_2])).
% 3.55/1.54  tff(c_128, plain, (![A_63]: (k1_funct_1(A_63, '#skF_2'(A_63))=k1_funct_1(A_63, '#skF_3'(A_63)) | v2_funct_1(A_63) | ~v1_funct_1(A_63) | ~v1_relat_1(A_63))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.55/1.54  tff(c_56, plain, (![D_31, C_30]: (v2_funct_1('#skF_5') | D_31=C_30 | k1_funct_1('#skF_5', D_31)!=k1_funct_1('#skF_5', C_30) | ~r2_hidden(D_31, '#skF_4') | ~r2_hidden(C_30, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.55/1.54  tff(c_86, plain, (![D_31, C_30]: (D_31=C_30 | k1_funct_1('#skF_5', D_31)!=k1_funct_1('#skF_5', C_30) | ~r2_hidden(D_31, '#skF_4') | ~r2_hidden(C_30, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_58, c_56])).
% 3.55/1.54  tff(c_137, plain, (![D_31]: (D_31='#skF_2'('#skF_5') | k1_funct_1('#skF_5', D_31)!=k1_funct_1('#skF_5', '#skF_3'('#skF_5')) | ~r2_hidden(D_31, '#skF_4') | ~r2_hidden('#skF_2'('#skF_5'), '#skF_4') | v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_128, c_86])).
% 3.55/1.54  tff(c_146, plain, (![D_31]: (D_31='#skF_2'('#skF_5') | k1_funct_1('#skF_5', D_31)!=k1_funct_1('#skF_5', '#skF_3'('#skF_5')) | ~r2_hidden(D_31, '#skF_4') | ~r2_hidden('#skF_2'('#skF_5'), '#skF_4') | v2_funct_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_63, c_36, c_137])).
% 3.55/1.54  tff(c_147, plain, (![D_31]: (D_31='#skF_2'('#skF_5') | k1_funct_1('#skF_5', D_31)!=k1_funct_1('#skF_5', '#skF_3'('#skF_5')) | ~r2_hidden(D_31, '#skF_4') | ~r2_hidden('#skF_2'('#skF_5'), '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_58, c_146])).
% 3.55/1.54  tff(c_204, plain, (~r2_hidden('#skF_2'('#skF_5'), '#skF_4')), inference(splitLeft, [status(thm)], [c_147])).
% 3.55/1.54  tff(c_207, plain, (~r1_tarski(k1_relat_1('#skF_5'), '#skF_4') | v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_114, c_204])).
% 3.55/1.54  tff(c_210, plain, (~r1_tarski(k1_relat_1('#skF_5'), '#skF_4') | v2_funct_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_63, c_36, c_207])).
% 3.55/1.54  tff(c_211, plain, (~r1_tarski(k1_relat_1('#skF_5'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_58, c_210])).
% 3.55/1.54  tff(c_217, plain, (~v4_relat_1('#skF_5', '#skF_4') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_12, c_211])).
% 3.55/1.54  tff(c_224, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_63, c_76, c_217])).
% 3.55/1.54  tff(c_226, plain, (r2_hidden('#skF_2'('#skF_5'), '#skF_4')), inference(splitRight, [status(thm)], [c_147])).
% 3.55/1.54  tff(c_134, plain, (![C_30]: (C_30='#skF_2'('#skF_5') | k1_funct_1('#skF_5', C_30)!=k1_funct_1('#skF_5', '#skF_3'('#skF_5')) | ~r2_hidden('#skF_2'('#skF_5'), '#skF_4') | ~r2_hidden(C_30, '#skF_4') | v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_128, c_86])).
% 3.55/1.54  tff(c_143, plain, (![C_30]: (C_30='#skF_2'('#skF_5') | k1_funct_1('#skF_5', C_30)!=k1_funct_1('#skF_5', '#skF_3'('#skF_5')) | ~r2_hidden('#skF_2'('#skF_5'), '#skF_4') | ~r2_hidden(C_30, '#skF_4') | v2_funct_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_63, c_36, c_134])).
% 3.55/1.54  tff(c_144, plain, (![C_30]: (C_30='#skF_2'('#skF_5') | k1_funct_1('#skF_5', C_30)!=k1_funct_1('#skF_5', '#skF_3'('#skF_5')) | ~r2_hidden('#skF_2'('#skF_5'), '#skF_4') | ~r2_hidden(C_30, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_58, c_143])).
% 3.55/1.54  tff(c_258, plain, (![C_30]: (C_30='#skF_2'('#skF_5') | k1_funct_1('#skF_5', C_30)!=k1_funct_1('#skF_5', '#skF_3'('#skF_5')) | ~r2_hidden(C_30, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_226, c_144])).
% 3.55/1.54  tff(c_261, plain, ('#skF_2'('#skF_5')='#skF_3'('#skF_5') | ~r2_hidden('#skF_3'('#skF_5'), '#skF_4')), inference(reflexivity, [status(thm), theory('equality')], [c_258])).
% 3.55/1.54  tff(c_262, plain, (~r2_hidden('#skF_3'('#skF_5'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_110, c_261])).
% 3.55/1.54  tff(c_274, plain, (~r1_tarski(k1_relat_1('#skF_5'), '#skF_4') | v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_118, c_262])).
% 3.55/1.54  tff(c_277, plain, (~r1_tarski(k1_relat_1('#skF_5'), '#skF_4') | v2_funct_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_63, c_36, c_274])).
% 3.55/1.54  tff(c_278, plain, (~r1_tarski(k1_relat_1('#skF_5'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_58, c_277])).
% 3.55/1.54  tff(c_284, plain, (~v4_relat_1('#skF_5', '#skF_4') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_12, c_278])).
% 3.55/1.54  tff(c_291, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_63, c_76, c_284])).
% 3.55/1.54  tff(c_292, plain, ('#skF_7'!='#skF_6'), inference(splitRight, [status(thm)], [c_38])).
% 3.55/1.54  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.55/1.54  tff(c_310, plain, (![A_93, B_94]: (~r2_hidden('#skF_1'(A_93, B_94), B_94) | r1_tarski(A_93, B_94))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.55/1.54  tff(c_315, plain, (![A_1]: (r1_tarski(A_1, A_1))), inference(resolution, [status(thm)], [c_6, c_310])).
% 3.55/1.54  tff(c_34, plain, (v1_funct_2('#skF_5', '#skF_4', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.55/1.54  tff(c_293, plain, (v2_funct_1('#skF_5')), inference(splitRight, [status(thm)], [c_38])).
% 3.55/1.54  tff(c_40, plain, (k1_funct_1('#skF_5', '#skF_7')=k1_funct_1('#skF_5', '#skF_6') | ~v2_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.55/1.54  tff(c_304, plain, (k1_funct_1('#skF_5', '#skF_7')=k1_funct_1('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_293, c_40])).
% 3.55/1.54  tff(c_42, plain, (r2_hidden('#skF_7', '#skF_4') | ~v2_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.55/1.54  tff(c_297, plain, (r2_hidden('#skF_7', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_293, c_42])).
% 3.55/1.54  tff(c_605, plain, (![D_178, C_179, B_180, A_181]: (k1_funct_1(k2_funct_1(D_178), k1_funct_1(D_178, C_179))=C_179 | k1_xboole_0=B_180 | ~r2_hidden(C_179, A_181) | ~v2_funct_1(D_178) | ~m1_subset_1(D_178, k1_zfmisc_1(k2_zfmisc_1(A_181, B_180))) | ~v1_funct_2(D_178, A_181, B_180) | ~v1_funct_1(D_178))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.55/1.54  tff(c_668, plain, (![D_187, B_188]: (k1_funct_1(k2_funct_1(D_187), k1_funct_1(D_187, '#skF_7'))='#skF_7' | k1_xboole_0=B_188 | ~v2_funct_1(D_187) | ~m1_subset_1(D_187, k1_zfmisc_1(k2_zfmisc_1('#skF_4', B_188))) | ~v1_funct_2(D_187, '#skF_4', B_188) | ~v1_funct_1(D_187))), inference(resolution, [status(thm)], [c_297, c_605])).
% 3.55/1.54  tff(c_670, plain, (k1_funct_1(k2_funct_1('#skF_5'), k1_funct_1('#skF_5', '#skF_7'))='#skF_7' | k1_xboole_0='#skF_4' | ~v2_funct_1('#skF_5') | ~v1_funct_2('#skF_5', '#skF_4', '#skF_4') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_32, c_668])).
% 3.55/1.54  tff(c_673, plain, (k1_funct_1(k2_funct_1('#skF_5'), k1_funct_1('#skF_5', '#skF_6'))='#skF_7' | k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_293, c_304, c_670])).
% 3.55/1.54  tff(c_674, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_673])).
% 3.55/1.54  tff(c_8, plain, (![A_6]: (r1_tarski(k1_xboole_0, A_6))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.55/1.54  tff(c_44, plain, (r2_hidden('#skF_6', '#skF_4') | ~v2_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.55/1.54  tff(c_295, plain, (r2_hidden('#skF_6', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_293, c_44])).
% 3.55/1.54  tff(c_327, plain, (![C_102, B_103, A_104]: (r2_hidden(C_102, B_103) | ~r2_hidden(C_102, A_104) | ~r1_tarski(A_104, B_103))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.55/1.54  tff(c_342, plain, (![B_106]: (r2_hidden('#skF_6', B_106) | ~r1_tarski('#skF_4', B_106))), inference(resolution, [status(thm)], [c_295, c_327])).
% 3.55/1.54  tff(c_359, plain, (![B_113, B_114]: (r2_hidden('#skF_6', B_113) | ~r1_tarski(B_114, B_113) | ~r1_tarski('#skF_4', B_114))), inference(resolution, [status(thm)], [c_342, c_2])).
% 3.55/1.54  tff(c_368, plain, (![A_6]: (r2_hidden('#skF_6', A_6) | ~r1_tarski('#skF_4', k1_xboole_0))), inference(resolution, [status(thm)], [c_8, c_359])).
% 3.55/1.54  tff(c_369, plain, (~r1_tarski('#skF_4', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_368])).
% 3.55/1.54  tff(c_685, plain, (~r1_tarski('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_674, c_369])).
% 3.55/1.54  tff(c_689, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_315, c_685])).
% 3.55/1.54  tff(c_691, plain, (k1_xboole_0!='#skF_4'), inference(splitRight, [status(thm)], [c_673])).
% 3.55/1.54  tff(c_690, plain, (k1_funct_1(k2_funct_1('#skF_5'), k1_funct_1('#skF_5', '#skF_6'))='#skF_7'), inference(splitRight, [status(thm)], [c_673])).
% 3.55/1.54  tff(c_709, plain, (![D_192, B_193]: (k1_funct_1(k2_funct_1(D_192), k1_funct_1(D_192, '#skF_6'))='#skF_6' | k1_xboole_0=B_193 | ~v2_funct_1(D_192) | ~m1_subset_1(D_192, k1_zfmisc_1(k2_zfmisc_1('#skF_4', B_193))) | ~v1_funct_2(D_192, '#skF_4', B_193) | ~v1_funct_1(D_192))), inference(resolution, [status(thm)], [c_295, c_605])).
% 3.55/1.54  tff(c_711, plain, (k1_funct_1(k2_funct_1('#skF_5'), k1_funct_1('#skF_5', '#skF_6'))='#skF_6' | k1_xboole_0='#skF_4' | ~v2_funct_1('#skF_5') | ~v1_funct_2('#skF_5', '#skF_4', '#skF_4') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_32, c_709])).
% 3.55/1.54  tff(c_714, plain, ('#skF_7'='#skF_6' | k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_293, c_690, c_711])).
% 3.55/1.54  tff(c_716, plain, $false, inference(negUnitSimplification, [status(thm)], [c_691, c_292, c_714])).
% 3.55/1.54  tff(c_717, plain, (![A_6]: (r2_hidden('#skF_6', A_6))), inference(splitRight, [status(thm)], [c_368])).
% 3.55/1.54  tff(c_298, plain, (![C_88, A_89, B_90]: (v1_relat_1(C_88) | ~m1_subset_1(C_88, k1_zfmisc_1(k2_zfmisc_1(A_89, B_90))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.55/1.54  tff(c_302, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_32, c_298])).
% 3.55/1.54  tff(c_718, plain, (r1_tarski('#skF_4', k1_xboole_0)), inference(splitRight, [status(thm)], [c_368])).
% 3.55/1.54  tff(c_338, plain, (![B_105]: (r2_hidden('#skF_7', B_105) | ~r1_tarski('#skF_4', B_105))), inference(resolution, [status(thm)], [c_297, c_327])).
% 3.55/1.54  tff(c_727, plain, (![B_195, B_196]: (r2_hidden('#skF_7', B_195) | ~r1_tarski(B_196, B_195) | ~r1_tarski('#skF_4', B_196))), inference(resolution, [status(thm)], [c_338, c_2])).
% 3.55/1.54  tff(c_735, plain, (![A_6]: (r2_hidden('#skF_7', A_6) | ~r1_tarski('#skF_4', k1_xboole_0))), inference(resolution, [status(thm)], [c_8, c_727])).
% 3.55/1.54  tff(c_743, plain, (![A_6]: (r2_hidden('#skF_7', A_6))), inference(demodulation, [status(thm), theory('equality')], [c_718, c_735])).
% 3.55/1.54  tff(c_927, plain, (![C_231, B_232, A_233]: (C_231=B_232 | k1_funct_1(A_233, C_231)!=k1_funct_1(A_233, B_232) | ~r2_hidden(C_231, k1_relat_1(A_233)) | ~r2_hidden(B_232, k1_relat_1(A_233)) | ~v2_funct_1(A_233) | ~v1_funct_1(A_233) | ~v1_relat_1(A_233))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.55/1.54  tff(c_933, plain, (![B_232]: (B_232='#skF_7' | k1_funct_1('#skF_5', B_232)!=k1_funct_1('#skF_5', '#skF_6') | ~r2_hidden('#skF_7', k1_relat_1('#skF_5')) | ~r2_hidden(B_232, k1_relat_1('#skF_5')) | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_304, c_927])).
% 3.55/1.54  tff(c_975, plain, (![B_237]: (B_237='#skF_7' | k1_funct_1('#skF_5', B_237)!=k1_funct_1('#skF_5', '#skF_6') | ~r2_hidden(B_237, k1_relat_1('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_302, c_36, c_293, c_743, c_933])).
% 3.55/1.54  tff(c_1003, plain, ('#skF_7'='#skF_6'), inference(resolution, [status(thm)], [c_717, c_975])).
% 3.55/1.54  tff(c_1024, plain, $false, inference(negUnitSimplification, [status(thm)], [c_292, c_1003])).
% 3.55/1.54  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.55/1.54  
% 3.55/1.54  Inference rules
% 3.55/1.54  ----------------------
% 3.55/1.54  #Ref     : 5
% 3.55/1.54  #Sup     : 207
% 3.55/1.54  #Fact    : 0
% 3.55/1.54  #Define  : 0
% 3.55/1.54  #Split   : 7
% 3.55/1.54  #Chain   : 0
% 3.55/1.54  #Close   : 0
% 3.55/1.54  
% 3.55/1.54  Ordering : KBO
% 3.55/1.54  
% 3.55/1.54  Simplification rules
% 3.55/1.54  ----------------------
% 3.55/1.54  #Subsume      : 52
% 3.55/1.54  #Demod        : 106
% 3.55/1.54  #Tautology    : 64
% 3.55/1.54  #SimpNegUnit  : 9
% 3.55/1.54  #BackRed      : 12
% 3.55/1.54  
% 3.55/1.54  #Partial instantiations: 0
% 3.55/1.54  #Strategies tried      : 1
% 3.55/1.54  
% 3.55/1.54  Timing (in seconds)
% 3.55/1.54  ----------------------
% 3.55/1.54  Preprocessing        : 0.34
% 3.55/1.54  Parsing              : 0.17
% 3.55/1.54  CNF conversion       : 0.02
% 3.55/1.54  Main loop            : 0.45
% 3.55/1.55  Inferencing          : 0.17
% 3.55/1.55  Reduction            : 0.12
% 3.55/1.55  Demodulation         : 0.08
% 3.55/1.55  BG Simplification    : 0.02
% 3.55/1.55  Subsumption          : 0.09
% 3.55/1.55  Abstraction          : 0.02
% 3.55/1.55  MUC search           : 0.00
% 3.55/1.55  Cooper               : 0.00
% 3.55/1.55  Total                : 0.82
% 3.55/1.55  Index Insertion      : 0.00
% 3.55/1.55  Index Deletion       : 0.00
% 3.55/1.55  Index Matching       : 0.00
% 3.55/1.55  BG Taut test         : 0.00
%------------------------------------------------------------------------------
