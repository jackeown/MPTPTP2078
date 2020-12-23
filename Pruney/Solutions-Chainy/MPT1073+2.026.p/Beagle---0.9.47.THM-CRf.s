%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:18:01 EST 2020

% Result     : Theorem 3.35s
% Output     : CNFRefutation 3.76s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 109 expanded)
%              Number of leaves         :   34 (  56 expanded)
%              Depth                    :    7
%              Number of atoms          :  110 ( 252 expanded)
%              Number of equality atoms :   23 (  46 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_4 > #skF_7 > #skF_6 > #skF_2 > #skF_9 > #skF_8 > #skF_5 > #skF_3

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

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

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

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i * $i ) > $i )).

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

tff(f_91,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,B,C)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
       => ~ ( r2_hidden(A,k2_relset_1(B,C,D))
            & ! [E] :
                ( m1_subset_1(E,B)
               => A != k1_funct_1(D,E) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t190_funct_2)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_61,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_funct_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_69,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( k7_relset_1(A,B,C,A) = k2_relset_1(A,B,C)
        & k8_relset_1(A,B,C,B) = k1_relset_1(A,B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_relset_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(c_50,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_7','#skF_8'))) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_107,plain,(
    ! [C_72,A_73,B_74] :
      ( v1_relat_1(C_72)
      | ~ m1_subset_1(C_72,k1_zfmisc_1(k2_zfmisc_1(A_73,B_74))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_121,plain,(
    v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_50,c_107])).

tff(c_54,plain,(
    v1_funct_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_16,plain,(
    ! [A_7,B_30,D_45] :
      ( k1_funct_1(A_7,'#skF_5'(A_7,B_30,k9_relat_1(A_7,B_30),D_45)) = D_45
      | ~ r2_hidden(D_45,k9_relat_1(A_7,B_30))
      | ~ v1_funct_1(A_7)
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_10,plain,(
    ! [B_6,A_5] :
      ( m1_subset_1(B_6,A_5)
      | ~ v1_xboole_0(B_6)
      | ~ v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_75,plain,(
    ! [E_68] :
      ( k1_funct_1('#skF_9',E_68) != '#skF_6'
      | ~ m1_subset_1(E_68,'#skF_7') ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_80,plain,(
    ! [B_6] :
      ( k1_funct_1('#skF_9',B_6) != '#skF_6'
      | ~ v1_xboole_0(B_6)
      | ~ v1_xboole_0('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_10,c_75])).

tff(c_123,plain,(
    ~ v1_xboole_0('#skF_7') ),
    inference(splitLeft,[status(thm)],[c_80])).

tff(c_223,plain,(
    ! [A_95,B_96,D_97] :
      ( r2_hidden('#skF_5'(A_95,B_96,k9_relat_1(A_95,B_96),D_97),B_96)
      | ~ r2_hidden(D_97,k9_relat_1(A_95,B_96))
      | ~ v1_funct_1(A_95)
      | ~ v1_relat_1(A_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_6,plain,(
    ! [B_6,A_5] :
      ( m1_subset_1(B_6,A_5)
      | ~ r2_hidden(B_6,A_5)
      | v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_933,plain,(
    ! [A_231,B_232,D_233] :
      ( m1_subset_1('#skF_5'(A_231,B_232,k9_relat_1(A_231,B_232),D_233),B_232)
      | v1_xboole_0(B_232)
      | ~ r2_hidden(D_233,k9_relat_1(A_231,B_232))
      | ~ v1_funct_1(A_231)
      | ~ v1_relat_1(A_231) ) ),
    inference(resolution,[status(thm)],[c_223,c_6])).

tff(c_46,plain,(
    ! [E_60] :
      ( k1_funct_1('#skF_9',E_60) != '#skF_6'
      | ~ m1_subset_1(E_60,'#skF_7') ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_950,plain,(
    ! [A_231,D_233] :
      ( k1_funct_1('#skF_9','#skF_5'(A_231,'#skF_7',k9_relat_1(A_231,'#skF_7'),D_233)) != '#skF_6'
      | v1_xboole_0('#skF_7')
      | ~ r2_hidden(D_233,k9_relat_1(A_231,'#skF_7'))
      | ~ v1_funct_1(A_231)
      | ~ v1_relat_1(A_231) ) ),
    inference(resolution,[status(thm)],[c_933,c_46])).

tff(c_970,plain,(
    ! [A_234,D_235] :
      ( k1_funct_1('#skF_9','#skF_5'(A_234,'#skF_7',k9_relat_1(A_234,'#skF_7'),D_235)) != '#skF_6'
      | ~ r2_hidden(D_235,k9_relat_1(A_234,'#skF_7'))
      | ~ v1_funct_1(A_234)
      | ~ v1_relat_1(A_234) ) ),
    inference(negUnitSimplification,[status(thm)],[c_123,c_950])).

tff(c_974,plain,(
    ! [D_45] :
      ( D_45 != '#skF_6'
      | ~ r2_hidden(D_45,k9_relat_1('#skF_9','#skF_7'))
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9')
      | ~ r2_hidden(D_45,k9_relat_1('#skF_9','#skF_7'))
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_970])).

tff(c_977,plain,(
    ~ r2_hidden('#skF_6',k9_relat_1('#skF_9','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_121,c_54,c_121,c_54,c_974])).

tff(c_137,plain,(
    ! [A_81,B_82,C_83,D_84] :
      ( k7_relset_1(A_81,B_82,C_83,D_84) = k9_relat_1(C_83,D_84)
      | ~ m1_subset_1(C_83,k1_zfmisc_1(k2_zfmisc_1(A_81,B_82))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_150,plain,(
    ! [D_84] : k7_relset_1('#skF_7','#skF_8','#skF_9',D_84) = k9_relat_1('#skF_9',D_84) ),
    inference(resolution,[status(thm)],[c_50,c_137])).

tff(c_178,plain,(
    ! [A_89,B_90,C_91] :
      ( k7_relset_1(A_89,B_90,C_91,A_89) = k2_relset_1(A_89,B_90,C_91)
      | ~ m1_subset_1(C_91,k1_zfmisc_1(k2_zfmisc_1(A_89,B_90))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_186,plain,(
    k7_relset_1('#skF_7','#skF_8','#skF_9','#skF_7') = k2_relset_1('#skF_7','#skF_8','#skF_9') ),
    inference(resolution,[status(thm)],[c_50,c_178])).

tff(c_192,plain,(
    k2_relset_1('#skF_7','#skF_8','#skF_9') = k9_relat_1('#skF_9','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_150,c_186])).

tff(c_48,plain,(
    r2_hidden('#skF_6',k2_relset_1('#skF_7','#skF_8','#skF_9')) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_195,plain,(
    r2_hidden('#skF_6',k9_relat_1('#skF_9','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_192,c_48])).

tff(c_979,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_977,c_195])).

tff(c_981,plain,(
    v1_xboole_0('#skF_7') ),
    inference(splitRight,[status(thm)],[c_80])).

tff(c_997,plain,(
    ! [A_239,B_240,C_241,D_242] :
      ( k7_relset_1(A_239,B_240,C_241,D_242) = k9_relat_1(C_241,D_242)
      | ~ m1_subset_1(C_241,k1_zfmisc_1(k2_zfmisc_1(A_239,B_240))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_1008,plain,(
    ! [D_242] : k7_relset_1('#skF_7','#skF_8','#skF_9',D_242) = k9_relat_1('#skF_9',D_242) ),
    inference(resolution,[status(thm)],[c_50,c_997])).

tff(c_1039,plain,(
    ! [A_251,B_252,C_253] :
      ( k7_relset_1(A_251,B_252,C_253,A_251) = k2_relset_1(A_251,B_252,C_253)
      | ~ m1_subset_1(C_253,k1_zfmisc_1(k2_zfmisc_1(A_251,B_252))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_1047,plain,(
    k7_relset_1('#skF_7','#skF_8','#skF_9','#skF_7') = k2_relset_1('#skF_7','#skF_8','#skF_9') ),
    inference(resolution,[status(thm)],[c_50,c_1039])).

tff(c_1053,plain,(
    k2_relset_1('#skF_7','#skF_8','#skF_9') = k9_relat_1('#skF_9','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1008,c_1047])).

tff(c_1056,plain,(
    r2_hidden('#skF_6',k9_relat_1('#skF_9','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1053,c_48])).

tff(c_1085,plain,(
    ! [A_260,B_261,D_262] :
      ( r2_hidden('#skF_5'(A_260,B_261,k9_relat_1(A_260,B_261),D_262),B_261)
      | ~ r2_hidden(D_262,k9_relat_1(A_260,B_261))
      | ~ v1_funct_1(A_260)
      | ~ v1_relat_1(A_260) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1094,plain,(
    ! [B_263,D_264,A_265] :
      ( ~ v1_xboole_0(B_263)
      | ~ r2_hidden(D_264,k9_relat_1(A_265,B_263))
      | ~ v1_funct_1(A_265)
      | ~ v1_relat_1(A_265) ) ),
    inference(resolution,[status(thm)],[c_1085,c_2])).

tff(c_1101,plain,
    ( ~ v1_xboole_0('#skF_7')
    | ~ v1_funct_1('#skF_9')
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_1056,c_1094])).

tff(c_1117,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_121,c_54,c_981,c_1101])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n007.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 19:48:06 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.35/1.61  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.35/1.62  
% 3.35/1.62  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.35/1.62  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_4 > #skF_7 > #skF_6 > #skF_2 > #skF_9 > #skF_8 > #skF_5 > #skF_3
% 3.35/1.62  
% 3.35/1.62  %Foreground sorts:
% 3.35/1.62  
% 3.35/1.62  
% 3.35/1.62  %Background operators:
% 3.35/1.62  
% 3.35/1.62  
% 3.35/1.62  %Foreground operators:
% 3.35/1.62  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.35/1.62  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.35/1.62  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.35/1.62  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.35/1.62  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 3.35/1.62  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.35/1.62  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 3.35/1.62  tff('#skF_7', type, '#skF_7': $i).
% 3.35/1.62  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 3.35/1.62  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.35/1.62  tff('#skF_6', type, '#skF_6': $i).
% 3.35/1.62  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.35/1.62  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.35/1.62  tff('#skF_9', type, '#skF_9': $i).
% 3.35/1.62  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.35/1.62  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.35/1.62  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.35/1.62  tff('#skF_8', type, '#skF_8': $i).
% 3.35/1.62  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.35/1.62  tff('#skF_5', type, '#skF_5': ($i * $i * $i * $i) > $i).
% 3.35/1.62  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.35/1.62  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.35/1.62  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 3.35/1.62  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.35/1.62  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.35/1.62  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.35/1.62  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.35/1.62  
% 3.76/1.63  tff(f_91, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => ~(r2_hidden(A, k2_relset_1(B, C, D)) & (![E]: (m1_subset_1(E, B) => ~(A = k1_funct_1(D, E))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t190_funct_2)).
% 3.76/1.63  tff(f_65, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.76/1.63  tff(f_61, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: ((C = k9_relat_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E]: ((r2_hidden(E, k1_relat_1(A)) & r2_hidden(E, B)) & (D = k1_funct_1(A, E)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d12_funct_1)).
% 3.76/1.63  tff(f_44, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 3.76/1.63  tff(f_69, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 3.76/1.63  tff(f_75, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((k7_relset_1(A, B, C, A) = k2_relset_1(A, B, C)) & (k8_relset_1(A, B, C, B) = k1_relset_1(A, B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_relset_1)).
% 3.76/1.63  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 3.76/1.63  tff(c_50, plain, (m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_7', '#skF_8')))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.76/1.63  tff(c_107, plain, (![C_72, A_73, B_74]: (v1_relat_1(C_72) | ~m1_subset_1(C_72, k1_zfmisc_1(k2_zfmisc_1(A_73, B_74))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.76/1.63  tff(c_121, plain, (v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_50, c_107])).
% 3.76/1.63  tff(c_54, plain, (v1_funct_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.76/1.63  tff(c_16, plain, (![A_7, B_30, D_45]: (k1_funct_1(A_7, '#skF_5'(A_7, B_30, k9_relat_1(A_7, B_30), D_45))=D_45 | ~r2_hidden(D_45, k9_relat_1(A_7, B_30)) | ~v1_funct_1(A_7) | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.76/1.63  tff(c_10, plain, (![B_6, A_5]: (m1_subset_1(B_6, A_5) | ~v1_xboole_0(B_6) | ~v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.76/1.63  tff(c_75, plain, (![E_68]: (k1_funct_1('#skF_9', E_68)!='#skF_6' | ~m1_subset_1(E_68, '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.76/1.63  tff(c_80, plain, (![B_6]: (k1_funct_1('#skF_9', B_6)!='#skF_6' | ~v1_xboole_0(B_6) | ~v1_xboole_0('#skF_7'))), inference(resolution, [status(thm)], [c_10, c_75])).
% 3.76/1.63  tff(c_123, plain, (~v1_xboole_0('#skF_7')), inference(splitLeft, [status(thm)], [c_80])).
% 3.76/1.63  tff(c_223, plain, (![A_95, B_96, D_97]: (r2_hidden('#skF_5'(A_95, B_96, k9_relat_1(A_95, B_96), D_97), B_96) | ~r2_hidden(D_97, k9_relat_1(A_95, B_96)) | ~v1_funct_1(A_95) | ~v1_relat_1(A_95))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.76/1.63  tff(c_6, plain, (![B_6, A_5]: (m1_subset_1(B_6, A_5) | ~r2_hidden(B_6, A_5) | v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.76/1.63  tff(c_933, plain, (![A_231, B_232, D_233]: (m1_subset_1('#skF_5'(A_231, B_232, k9_relat_1(A_231, B_232), D_233), B_232) | v1_xboole_0(B_232) | ~r2_hidden(D_233, k9_relat_1(A_231, B_232)) | ~v1_funct_1(A_231) | ~v1_relat_1(A_231))), inference(resolution, [status(thm)], [c_223, c_6])).
% 3.76/1.63  tff(c_46, plain, (![E_60]: (k1_funct_1('#skF_9', E_60)!='#skF_6' | ~m1_subset_1(E_60, '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.76/1.63  tff(c_950, plain, (![A_231, D_233]: (k1_funct_1('#skF_9', '#skF_5'(A_231, '#skF_7', k9_relat_1(A_231, '#skF_7'), D_233))!='#skF_6' | v1_xboole_0('#skF_7') | ~r2_hidden(D_233, k9_relat_1(A_231, '#skF_7')) | ~v1_funct_1(A_231) | ~v1_relat_1(A_231))), inference(resolution, [status(thm)], [c_933, c_46])).
% 3.76/1.63  tff(c_970, plain, (![A_234, D_235]: (k1_funct_1('#skF_9', '#skF_5'(A_234, '#skF_7', k9_relat_1(A_234, '#skF_7'), D_235))!='#skF_6' | ~r2_hidden(D_235, k9_relat_1(A_234, '#skF_7')) | ~v1_funct_1(A_234) | ~v1_relat_1(A_234))), inference(negUnitSimplification, [status(thm)], [c_123, c_950])).
% 3.76/1.63  tff(c_974, plain, (![D_45]: (D_45!='#skF_6' | ~r2_hidden(D_45, k9_relat_1('#skF_9', '#skF_7')) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9') | ~r2_hidden(D_45, k9_relat_1('#skF_9', '#skF_7')) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_16, c_970])).
% 3.76/1.63  tff(c_977, plain, (~r2_hidden('#skF_6', k9_relat_1('#skF_9', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_121, c_54, c_121, c_54, c_974])).
% 3.76/1.63  tff(c_137, plain, (![A_81, B_82, C_83, D_84]: (k7_relset_1(A_81, B_82, C_83, D_84)=k9_relat_1(C_83, D_84) | ~m1_subset_1(C_83, k1_zfmisc_1(k2_zfmisc_1(A_81, B_82))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.76/1.63  tff(c_150, plain, (![D_84]: (k7_relset_1('#skF_7', '#skF_8', '#skF_9', D_84)=k9_relat_1('#skF_9', D_84))), inference(resolution, [status(thm)], [c_50, c_137])).
% 3.76/1.63  tff(c_178, plain, (![A_89, B_90, C_91]: (k7_relset_1(A_89, B_90, C_91, A_89)=k2_relset_1(A_89, B_90, C_91) | ~m1_subset_1(C_91, k1_zfmisc_1(k2_zfmisc_1(A_89, B_90))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.76/1.63  tff(c_186, plain, (k7_relset_1('#skF_7', '#skF_8', '#skF_9', '#skF_7')=k2_relset_1('#skF_7', '#skF_8', '#skF_9')), inference(resolution, [status(thm)], [c_50, c_178])).
% 3.76/1.63  tff(c_192, plain, (k2_relset_1('#skF_7', '#skF_8', '#skF_9')=k9_relat_1('#skF_9', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_150, c_186])).
% 3.76/1.63  tff(c_48, plain, (r2_hidden('#skF_6', k2_relset_1('#skF_7', '#skF_8', '#skF_9'))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.76/1.63  tff(c_195, plain, (r2_hidden('#skF_6', k9_relat_1('#skF_9', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_192, c_48])).
% 3.76/1.63  tff(c_979, plain, $false, inference(negUnitSimplification, [status(thm)], [c_977, c_195])).
% 3.76/1.63  tff(c_981, plain, (v1_xboole_0('#skF_7')), inference(splitRight, [status(thm)], [c_80])).
% 3.76/1.63  tff(c_997, plain, (![A_239, B_240, C_241, D_242]: (k7_relset_1(A_239, B_240, C_241, D_242)=k9_relat_1(C_241, D_242) | ~m1_subset_1(C_241, k1_zfmisc_1(k2_zfmisc_1(A_239, B_240))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.76/1.63  tff(c_1008, plain, (![D_242]: (k7_relset_1('#skF_7', '#skF_8', '#skF_9', D_242)=k9_relat_1('#skF_9', D_242))), inference(resolution, [status(thm)], [c_50, c_997])).
% 3.76/1.63  tff(c_1039, plain, (![A_251, B_252, C_253]: (k7_relset_1(A_251, B_252, C_253, A_251)=k2_relset_1(A_251, B_252, C_253) | ~m1_subset_1(C_253, k1_zfmisc_1(k2_zfmisc_1(A_251, B_252))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.76/1.63  tff(c_1047, plain, (k7_relset_1('#skF_7', '#skF_8', '#skF_9', '#skF_7')=k2_relset_1('#skF_7', '#skF_8', '#skF_9')), inference(resolution, [status(thm)], [c_50, c_1039])).
% 3.76/1.63  tff(c_1053, plain, (k2_relset_1('#skF_7', '#skF_8', '#skF_9')=k9_relat_1('#skF_9', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_1008, c_1047])).
% 3.76/1.63  tff(c_1056, plain, (r2_hidden('#skF_6', k9_relat_1('#skF_9', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_1053, c_48])).
% 3.76/1.63  tff(c_1085, plain, (![A_260, B_261, D_262]: (r2_hidden('#skF_5'(A_260, B_261, k9_relat_1(A_260, B_261), D_262), B_261) | ~r2_hidden(D_262, k9_relat_1(A_260, B_261)) | ~v1_funct_1(A_260) | ~v1_relat_1(A_260))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.76/1.63  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.76/1.63  tff(c_1094, plain, (![B_263, D_264, A_265]: (~v1_xboole_0(B_263) | ~r2_hidden(D_264, k9_relat_1(A_265, B_263)) | ~v1_funct_1(A_265) | ~v1_relat_1(A_265))), inference(resolution, [status(thm)], [c_1085, c_2])).
% 3.76/1.63  tff(c_1101, plain, (~v1_xboole_0('#skF_7') | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_1056, c_1094])).
% 3.76/1.63  tff(c_1117, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_121, c_54, c_981, c_1101])).
% 3.76/1.63  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.76/1.63  
% 3.76/1.63  Inference rules
% 3.76/1.63  ----------------------
% 3.76/1.63  #Ref     : 0
% 3.76/1.63  #Sup     : 226
% 3.76/1.63  #Fact    : 0
% 3.76/1.63  #Define  : 0
% 3.76/1.63  #Split   : 5
% 3.76/1.63  #Chain   : 0
% 3.76/1.63  #Close   : 0
% 3.76/1.63  
% 3.76/1.63  Ordering : KBO
% 3.76/1.63  
% 3.76/1.63  Simplification rules
% 3.76/1.63  ----------------------
% 3.76/1.63  #Subsume      : 41
% 3.76/1.63  #Demod        : 30
% 3.76/1.63  #Tautology    : 35
% 3.76/1.63  #SimpNegUnit  : 31
% 3.76/1.63  #BackRed      : 7
% 3.76/1.63  
% 3.76/1.63  #Partial instantiations: 0
% 3.76/1.63  #Strategies tried      : 1
% 3.76/1.63  
% 3.76/1.63  Timing (in seconds)
% 3.76/1.63  ----------------------
% 3.76/1.64  Preprocessing        : 0.34
% 3.76/1.64  Parsing              : 0.18
% 3.76/1.64  CNF conversion       : 0.03
% 3.76/1.64  Main loop            : 0.51
% 3.76/1.64  Inferencing          : 0.17
% 3.76/1.64  Reduction            : 0.11
% 3.76/1.64  Demodulation         : 0.07
% 3.76/1.64  BG Simplification    : 0.03
% 3.76/1.64  Subsumption          : 0.16
% 3.76/1.64  Abstraction          : 0.04
% 3.76/1.64  MUC search           : 0.00
% 3.76/1.64  Cooper               : 0.00
% 3.76/1.64  Total                : 0.88
% 3.76/1.64  Index Insertion      : 0.00
% 3.76/1.64  Index Deletion       : 0.00
% 3.76/1.64  Index Matching       : 0.00
% 3.76/1.64  BG Taut test         : 0.00
%------------------------------------------------------------------------------
