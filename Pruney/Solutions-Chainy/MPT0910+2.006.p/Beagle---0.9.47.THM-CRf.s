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
% DateTime   : Thu Dec  3 10:10:00 EST 2020

% Result     : Theorem 2.33s
% Output     : CNFRefutation 2.33s
% Verified   : 
% Statistics : Number of formulae       :   54 ( 142 expanded)
%              Number of leaves         :   25 (  68 expanded)
%              Depth                    :   16
%              Number of atoms          :  147 ( 673 expanded)
%              Number of equality atoms :   98 ( 420 expanded)
%              Maximal formula depth    :   18 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_subset_1 > k6_mcart_1 > k3_zfmisc_1 > k3_mcart_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_11 > #skF_2 > #skF_7 > #skF_10 > #skF_6 > #skF_9 > #skF_4 > #skF_3 > #skF_1 > #skF_8 > #skF_5

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff('#skF_11',type,(
    '#skF_11': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_mcart_1,type,(
    k3_mcart_1: ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k3_zfmisc_1,type,(
    k3_zfmisc_1: ( $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i * $i ) > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff(k6_mcart_1,type,(
    k6_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_106,negated_conjecture,(
    ~ ! [A,B,C,D,E] :
        ( m1_subset_1(E,k3_zfmisc_1(A,B,C))
       => ( ! [F] :
              ( m1_subset_1(F,A)
             => ! [G] :
                  ( m1_subset_1(G,B)
                 => ! [H] :
                      ( m1_subset_1(H,C)
                     => ( E = k3_mcart_1(F,G,H)
                       => D = G ) ) ) )
         => ( A = k1_xboole_0
            | B = k1_xboole_0
            | C = k1_xboole_0
            | D = k6_mcart_1(A,B,C,E) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_mcart_1)).

tff(f_82,axiom,(
    ! [A,B,C] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & C != k1_xboole_0
        & ? [D] :
            ( m1_subset_1(D,k3_zfmisc_1(A,B,C))
            & ! [E] :
                ( m1_subset_1(E,A)
               => ! [F] :
                    ( m1_subset_1(F,B)
                   => ! [G] :
                        ( m1_subset_1(G,C)
                       => D != k3_mcart_1(E,F,G) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l44_mcart_1)).

tff(f_57,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k3_zfmisc_1(A,B,C))
     => m1_subset_1(k6_mcart_1(A,B,C,D),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_mcart_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & C != k1_xboole_0
        & ~ ! [D] :
              ( m1_subset_1(D,k3_zfmisc_1(A,B,C))
             => ! [E] :
                  ( m1_subset_1(E,B)
                 => ( E = k6_mcart_1(A,B,C,D)
                  <=> ! [F,G,H] :
                        ( D = k3_mcart_1(F,G,H)
                       => E = G ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_mcart_1)).

tff(c_28,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_26,plain,(
    k1_xboole_0 != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_24,plain,(
    k1_xboole_0 != '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_22,plain,(
    k6_mcart_1('#skF_7','#skF_8','#skF_9','#skF_11') != '#skF_10' ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_32,plain,(
    m1_subset_1('#skF_11',k3_zfmisc_1('#skF_7','#skF_8','#skF_9')) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_18,plain,(
    ! [A_65,B_66,C_67,D_83] :
      ( m1_subset_1('#skF_5'(A_65,B_66,C_67,D_83),B_66)
      | ~ m1_subset_1(D_83,k3_zfmisc_1(A_65,B_66,C_67))
      | k1_xboole_0 = C_67
      | k1_xboole_0 = B_66
      | k1_xboole_0 = A_65 ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_20,plain,(
    ! [A_65,B_66,C_67,D_83] :
      ( m1_subset_1('#skF_4'(A_65,B_66,C_67,D_83),A_65)
      | ~ m1_subset_1(D_83,k3_zfmisc_1(A_65,B_66,C_67))
      | k1_xboole_0 = C_67
      | k1_xboole_0 = B_66
      | k1_xboole_0 = A_65 ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_16,plain,(
    ! [A_65,B_66,C_67,D_83] :
      ( m1_subset_1('#skF_6'(A_65,B_66,C_67,D_83),C_67)
      | ~ m1_subset_1(D_83,k3_zfmisc_1(A_65,B_66,C_67))
      | k1_xboole_0 = C_67
      | k1_xboole_0 = B_66
      | k1_xboole_0 = A_65 ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_109,plain,(
    ! [A_151,B_152,C_153,D_154] :
      ( k3_mcart_1('#skF_4'(A_151,B_152,C_153,D_154),'#skF_5'(A_151,B_152,C_153,D_154),'#skF_6'(A_151,B_152,C_153,D_154)) = D_154
      | ~ m1_subset_1(D_154,k3_zfmisc_1(A_151,B_152,C_153))
      | k1_xboole_0 = C_153
      | k1_xboole_0 = B_152
      | k1_xboole_0 = A_151 ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_30,plain,(
    ! [G_106,F_102,H_108] :
      ( G_106 = '#skF_10'
      | k3_mcart_1(F_102,G_106,H_108) != '#skF_11'
      | ~ m1_subset_1(H_108,'#skF_9')
      | ~ m1_subset_1(G_106,'#skF_8')
      | ~ m1_subset_1(F_102,'#skF_7') ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_123,plain,(
    ! [A_155,B_156,C_157,D_158] :
      ( '#skF_5'(A_155,B_156,C_157,D_158) = '#skF_10'
      | D_158 != '#skF_11'
      | ~ m1_subset_1('#skF_6'(A_155,B_156,C_157,D_158),'#skF_9')
      | ~ m1_subset_1('#skF_5'(A_155,B_156,C_157,D_158),'#skF_8')
      | ~ m1_subset_1('#skF_4'(A_155,B_156,C_157,D_158),'#skF_7')
      | ~ m1_subset_1(D_158,k3_zfmisc_1(A_155,B_156,C_157))
      | k1_xboole_0 = C_157
      | k1_xboole_0 = B_156
      | k1_xboole_0 = A_155 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_109,c_30])).

tff(c_127,plain,(
    ! [A_65,B_66,D_83] :
      ( '#skF_5'(A_65,B_66,'#skF_9',D_83) = '#skF_10'
      | D_83 != '#skF_11'
      | ~ m1_subset_1('#skF_5'(A_65,B_66,'#skF_9',D_83),'#skF_8')
      | ~ m1_subset_1('#skF_4'(A_65,B_66,'#skF_9',D_83),'#skF_7')
      | ~ m1_subset_1(D_83,k3_zfmisc_1(A_65,B_66,'#skF_9'))
      | k1_xboole_0 = '#skF_9'
      | k1_xboole_0 = B_66
      | k1_xboole_0 = A_65 ) ),
    inference(resolution,[status(thm)],[c_16,c_123])).

tff(c_132,plain,(
    ! [A_159,B_160,D_161] :
      ( '#skF_5'(A_159,B_160,'#skF_9',D_161) = '#skF_10'
      | D_161 != '#skF_11'
      | ~ m1_subset_1('#skF_5'(A_159,B_160,'#skF_9',D_161),'#skF_8')
      | ~ m1_subset_1('#skF_4'(A_159,B_160,'#skF_9',D_161),'#skF_7')
      | ~ m1_subset_1(D_161,k3_zfmisc_1(A_159,B_160,'#skF_9'))
      | k1_xboole_0 = B_160
      | k1_xboole_0 = A_159 ) ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_24,c_127])).

tff(c_136,plain,(
    ! [B_66,D_83] :
      ( '#skF_5'('#skF_7',B_66,'#skF_9',D_83) = '#skF_10'
      | D_83 != '#skF_11'
      | ~ m1_subset_1('#skF_5'('#skF_7',B_66,'#skF_9',D_83),'#skF_8')
      | ~ m1_subset_1(D_83,k3_zfmisc_1('#skF_7',B_66,'#skF_9'))
      | k1_xboole_0 = '#skF_9'
      | k1_xboole_0 = B_66
      | k1_xboole_0 = '#skF_7' ) ),
    inference(resolution,[status(thm)],[c_20,c_132])).

tff(c_141,plain,(
    ! [B_162,D_163] :
      ( '#skF_5'('#skF_7',B_162,'#skF_9',D_163) = '#skF_10'
      | D_163 != '#skF_11'
      | ~ m1_subset_1('#skF_5'('#skF_7',B_162,'#skF_9',D_163),'#skF_8')
      | ~ m1_subset_1(D_163,k3_zfmisc_1('#skF_7',B_162,'#skF_9'))
      | k1_xboole_0 = B_162 ) ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_24,c_28,c_136])).

tff(c_145,plain,(
    ! [D_83] :
      ( '#skF_5'('#skF_7','#skF_8','#skF_9',D_83) = '#skF_10'
      | D_83 != '#skF_11'
      | ~ m1_subset_1(D_83,k3_zfmisc_1('#skF_7','#skF_8','#skF_9'))
      | k1_xboole_0 = '#skF_9'
      | k1_xboole_0 = '#skF_8'
      | k1_xboole_0 = '#skF_7' ) ),
    inference(resolution,[status(thm)],[c_18,c_141])).

tff(c_150,plain,(
    ! [D_164] :
      ( '#skF_5'('#skF_7','#skF_8','#skF_9',D_164) = '#skF_10'
      | D_164 != '#skF_11'
      | ~ m1_subset_1(D_164,k3_zfmisc_1('#skF_7','#skF_8','#skF_9')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_26,c_24,c_26,c_145])).

tff(c_174,plain,(
    '#skF_5'('#skF_7','#skF_8','#skF_9','#skF_11') = '#skF_10' ),
    inference(resolution,[status(thm)],[c_32,c_150])).

tff(c_14,plain,(
    ! [A_65,B_66,C_67,D_83] :
      ( k3_mcart_1('#skF_4'(A_65,B_66,C_67,D_83),'#skF_5'(A_65,B_66,C_67,D_83),'#skF_6'(A_65,B_66,C_67,D_83)) = D_83
      | ~ m1_subset_1(D_83,k3_zfmisc_1(A_65,B_66,C_67))
      | k1_xboole_0 = C_67
      | k1_xboole_0 = B_66
      | k1_xboole_0 = A_65 ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_181,plain,
    ( k3_mcart_1('#skF_4'('#skF_7','#skF_8','#skF_9','#skF_11'),'#skF_10','#skF_6'('#skF_7','#skF_8','#skF_9','#skF_11')) = '#skF_11'
    | ~ m1_subset_1('#skF_11',k3_zfmisc_1('#skF_7','#skF_8','#skF_9'))
    | k1_xboole_0 = '#skF_9'
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7' ),
    inference(superposition,[status(thm),theory(equality)],[c_174,c_14])).

tff(c_192,plain,
    ( k3_mcart_1('#skF_4'('#skF_7','#skF_8','#skF_9','#skF_11'),'#skF_10','#skF_6'('#skF_7','#skF_8','#skF_9','#skF_11')) = '#skF_11'
    | k1_xboole_0 = '#skF_9'
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_181])).

tff(c_193,plain,(
    k3_mcart_1('#skF_4'('#skF_7','#skF_8','#skF_9','#skF_11'),'#skF_10','#skF_6'('#skF_7','#skF_8','#skF_9','#skF_11')) = '#skF_11' ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_26,c_24,c_192])).

tff(c_12,plain,(
    ! [A_61,B_62,C_63,D_64] :
      ( m1_subset_1(k6_mcart_1(A_61,B_62,C_63,D_64),B_62)
      | ~ m1_subset_1(D_64,k3_zfmisc_1(A_61,B_62,C_63)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_198,plain,(
    ! [B_166,G_165,H_170,C_167,A_168,F_169] :
      ( k6_mcart_1(A_168,B_166,C_167,k3_mcart_1(F_169,G_165,H_170)) = G_165
      | ~ m1_subset_1(k6_mcart_1(A_168,B_166,C_167,k3_mcart_1(F_169,G_165,H_170)),B_166)
      | ~ m1_subset_1(k3_mcart_1(F_169,G_165,H_170),k3_zfmisc_1(A_168,B_166,C_167))
      | k1_xboole_0 = C_167
      | k1_xboole_0 = B_166
      | k1_xboole_0 = A_168 ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_227,plain,(
    ! [H_171,G_172,B_174,C_173,A_175,F_176] :
      ( k6_mcart_1(A_175,B_174,C_173,k3_mcart_1(F_176,G_172,H_171)) = G_172
      | k1_xboole_0 = C_173
      | k1_xboole_0 = B_174
      | k1_xboole_0 = A_175
      | ~ m1_subset_1(k3_mcart_1(F_176,G_172,H_171),k3_zfmisc_1(A_175,B_174,C_173)) ) ),
    inference(resolution,[status(thm)],[c_12,c_198])).

tff(c_230,plain,(
    ! [A_175,B_174,C_173] :
      ( k6_mcart_1(A_175,B_174,C_173,k3_mcart_1('#skF_4'('#skF_7','#skF_8','#skF_9','#skF_11'),'#skF_10','#skF_6'('#skF_7','#skF_8','#skF_9','#skF_11'))) = '#skF_10'
      | k1_xboole_0 = C_173
      | k1_xboole_0 = B_174
      | k1_xboole_0 = A_175
      | ~ m1_subset_1('#skF_11',k3_zfmisc_1(A_175,B_174,C_173)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_193,c_227])).

tff(c_242,plain,(
    ! [A_177,B_178,C_179] :
      ( k6_mcart_1(A_177,B_178,C_179,'#skF_11') = '#skF_10'
      | k1_xboole_0 = C_179
      | k1_xboole_0 = B_178
      | k1_xboole_0 = A_177
      | ~ m1_subset_1('#skF_11',k3_zfmisc_1(A_177,B_178,C_179)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_193,c_230])).

tff(c_248,plain,
    ( k6_mcart_1('#skF_7','#skF_8','#skF_9','#skF_11') = '#skF_10'
    | k1_xboole_0 = '#skF_9'
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7' ),
    inference(resolution,[status(thm)],[c_32,c_242])).

tff(c_252,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_26,c_24,c_22,c_248])).
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
% 0.13/0.34  % DateTime   : Tue Dec  1 10:08:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.33/1.28  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.33/1.29  
% 2.33/1.29  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.33/1.29  %$ m1_subset_1 > k6_mcart_1 > k3_zfmisc_1 > k3_mcart_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_11 > #skF_2 > #skF_7 > #skF_10 > #skF_6 > #skF_9 > #skF_4 > #skF_3 > #skF_1 > #skF_8 > #skF_5
% 2.33/1.29  
% 2.33/1.29  %Foreground sorts:
% 2.33/1.29  
% 2.33/1.29  
% 2.33/1.29  %Background operators:
% 2.33/1.29  
% 2.33/1.29  
% 2.33/1.29  %Foreground operators:
% 2.33/1.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.33/1.29  tff('#skF_11', type, '#skF_11': $i).
% 2.33/1.29  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i * $i) > $i).
% 2.33/1.29  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.33/1.29  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.33/1.29  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 2.33/1.29  tff('#skF_7', type, '#skF_7': $i).
% 2.33/1.29  tff('#skF_10', type, '#skF_10': $i).
% 2.33/1.29  tff('#skF_6', type, '#skF_6': ($i * $i * $i * $i) > $i).
% 2.33/1.29  tff('#skF_9', type, '#skF_9': $i).
% 2.33/1.29  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 2.33/1.29  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 2.33/1.29  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i * $i) > $i).
% 2.33/1.29  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i * $i) > $i).
% 2.33/1.29  tff('#skF_8', type, '#skF_8': $i).
% 2.33/1.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.33/1.29  tff('#skF_5', type, '#skF_5': ($i * $i * $i * $i) > $i).
% 2.33/1.29  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.33/1.29  tff(k6_mcart_1, type, k6_mcart_1: ($i * $i * $i * $i) > $i).
% 2.33/1.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.33/1.29  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.33/1.29  
% 2.33/1.30  tff(f_106, negated_conjecture, ~(![A, B, C, D, E]: (m1_subset_1(E, k3_zfmisc_1(A, B, C)) => ((![F]: (m1_subset_1(F, A) => (![G]: (m1_subset_1(G, B) => (![H]: (m1_subset_1(H, C) => ((E = k3_mcart_1(F, G, H)) => (D = G)))))))) => ((((A = k1_xboole_0) | (B = k1_xboole_0)) | (C = k1_xboole_0)) | (D = k6_mcart_1(A, B, C, E)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_mcart_1)).
% 2.33/1.30  tff(f_82, axiom, (![A, B, C]: ~(((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & (?[D]: (m1_subset_1(D, k3_zfmisc_1(A, B, C)) & (![E]: (m1_subset_1(E, A) => (![F]: (m1_subset_1(F, B) => (![G]: (m1_subset_1(G, C) => ~(D = k3_mcart_1(E, F, G)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l44_mcart_1)).
% 2.33/1.30  tff(f_57, axiom, (![A, B, C, D]: (m1_subset_1(D, k3_zfmisc_1(A, B, C)) => m1_subset_1(k6_mcart_1(A, B, C, D), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_mcart_1)).
% 2.33/1.30  tff(f_53, axiom, (![A, B, C]: ~(((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(![D]: (m1_subset_1(D, k3_zfmisc_1(A, B, C)) => (![E]: (m1_subset_1(E, B) => ((E = k6_mcart_1(A, B, C, D)) <=> (![F, G, H]: ((D = k3_mcart_1(F, G, H)) => (E = G)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_mcart_1)).
% 2.33/1.30  tff(c_28, plain, (k1_xboole_0!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_106])).
% 2.33/1.30  tff(c_26, plain, (k1_xboole_0!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_106])).
% 2.33/1.30  tff(c_24, plain, (k1_xboole_0!='#skF_9'), inference(cnfTransformation, [status(thm)], [f_106])).
% 2.33/1.30  tff(c_22, plain, (k6_mcart_1('#skF_7', '#skF_8', '#skF_9', '#skF_11')!='#skF_10'), inference(cnfTransformation, [status(thm)], [f_106])).
% 2.33/1.30  tff(c_32, plain, (m1_subset_1('#skF_11', k3_zfmisc_1('#skF_7', '#skF_8', '#skF_9'))), inference(cnfTransformation, [status(thm)], [f_106])).
% 2.33/1.30  tff(c_18, plain, (![A_65, B_66, C_67, D_83]: (m1_subset_1('#skF_5'(A_65, B_66, C_67, D_83), B_66) | ~m1_subset_1(D_83, k3_zfmisc_1(A_65, B_66, C_67)) | k1_xboole_0=C_67 | k1_xboole_0=B_66 | k1_xboole_0=A_65)), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.33/1.30  tff(c_20, plain, (![A_65, B_66, C_67, D_83]: (m1_subset_1('#skF_4'(A_65, B_66, C_67, D_83), A_65) | ~m1_subset_1(D_83, k3_zfmisc_1(A_65, B_66, C_67)) | k1_xboole_0=C_67 | k1_xboole_0=B_66 | k1_xboole_0=A_65)), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.33/1.30  tff(c_16, plain, (![A_65, B_66, C_67, D_83]: (m1_subset_1('#skF_6'(A_65, B_66, C_67, D_83), C_67) | ~m1_subset_1(D_83, k3_zfmisc_1(A_65, B_66, C_67)) | k1_xboole_0=C_67 | k1_xboole_0=B_66 | k1_xboole_0=A_65)), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.33/1.30  tff(c_109, plain, (![A_151, B_152, C_153, D_154]: (k3_mcart_1('#skF_4'(A_151, B_152, C_153, D_154), '#skF_5'(A_151, B_152, C_153, D_154), '#skF_6'(A_151, B_152, C_153, D_154))=D_154 | ~m1_subset_1(D_154, k3_zfmisc_1(A_151, B_152, C_153)) | k1_xboole_0=C_153 | k1_xboole_0=B_152 | k1_xboole_0=A_151)), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.33/1.30  tff(c_30, plain, (![G_106, F_102, H_108]: (G_106='#skF_10' | k3_mcart_1(F_102, G_106, H_108)!='#skF_11' | ~m1_subset_1(H_108, '#skF_9') | ~m1_subset_1(G_106, '#skF_8') | ~m1_subset_1(F_102, '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_106])).
% 2.33/1.30  tff(c_123, plain, (![A_155, B_156, C_157, D_158]: ('#skF_5'(A_155, B_156, C_157, D_158)='#skF_10' | D_158!='#skF_11' | ~m1_subset_1('#skF_6'(A_155, B_156, C_157, D_158), '#skF_9') | ~m1_subset_1('#skF_5'(A_155, B_156, C_157, D_158), '#skF_8') | ~m1_subset_1('#skF_4'(A_155, B_156, C_157, D_158), '#skF_7') | ~m1_subset_1(D_158, k3_zfmisc_1(A_155, B_156, C_157)) | k1_xboole_0=C_157 | k1_xboole_0=B_156 | k1_xboole_0=A_155)), inference(superposition, [status(thm), theory('equality')], [c_109, c_30])).
% 2.33/1.30  tff(c_127, plain, (![A_65, B_66, D_83]: ('#skF_5'(A_65, B_66, '#skF_9', D_83)='#skF_10' | D_83!='#skF_11' | ~m1_subset_1('#skF_5'(A_65, B_66, '#skF_9', D_83), '#skF_8') | ~m1_subset_1('#skF_4'(A_65, B_66, '#skF_9', D_83), '#skF_7') | ~m1_subset_1(D_83, k3_zfmisc_1(A_65, B_66, '#skF_9')) | k1_xboole_0='#skF_9' | k1_xboole_0=B_66 | k1_xboole_0=A_65)), inference(resolution, [status(thm)], [c_16, c_123])).
% 2.33/1.30  tff(c_132, plain, (![A_159, B_160, D_161]: ('#skF_5'(A_159, B_160, '#skF_9', D_161)='#skF_10' | D_161!='#skF_11' | ~m1_subset_1('#skF_5'(A_159, B_160, '#skF_9', D_161), '#skF_8') | ~m1_subset_1('#skF_4'(A_159, B_160, '#skF_9', D_161), '#skF_7') | ~m1_subset_1(D_161, k3_zfmisc_1(A_159, B_160, '#skF_9')) | k1_xboole_0=B_160 | k1_xboole_0=A_159)), inference(negUnitSimplification, [status(thm)], [c_24, c_24, c_127])).
% 2.33/1.30  tff(c_136, plain, (![B_66, D_83]: ('#skF_5'('#skF_7', B_66, '#skF_9', D_83)='#skF_10' | D_83!='#skF_11' | ~m1_subset_1('#skF_5'('#skF_7', B_66, '#skF_9', D_83), '#skF_8') | ~m1_subset_1(D_83, k3_zfmisc_1('#skF_7', B_66, '#skF_9')) | k1_xboole_0='#skF_9' | k1_xboole_0=B_66 | k1_xboole_0='#skF_7')), inference(resolution, [status(thm)], [c_20, c_132])).
% 2.33/1.30  tff(c_141, plain, (![B_162, D_163]: ('#skF_5'('#skF_7', B_162, '#skF_9', D_163)='#skF_10' | D_163!='#skF_11' | ~m1_subset_1('#skF_5'('#skF_7', B_162, '#skF_9', D_163), '#skF_8') | ~m1_subset_1(D_163, k3_zfmisc_1('#skF_7', B_162, '#skF_9')) | k1_xboole_0=B_162)), inference(negUnitSimplification, [status(thm)], [c_28, c_24, c_28, c_136])).
% 2.33/1.30  tff(c_145, plain, (![D_83]: ('#skF_5'('#skF_7', '#skF_8', '#skF_9', D_83)='#skF_10' | D_83!='#skF_11' | ~m1_subset_1(D_83, k3_zfmisc_1('#skF_7', '#skF_8', '#skF_9')) | k1_xboole_0='#skF_9' | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7')), inference(resolution, [status(thm)], [c_18, c_141])).
% 2.33/1.30  tff(c_150, plain, (![D_164]: ('#skF_5'('#skF_7', '#skF_8', '#skF_9', D_164)='#skF_10' | D_164!='#skF_11' | ~m1_subset_1(D_164, k3_zfmisc_1('#skF_7', '#skF_8', '#skF_9')))), inference(negUnitSimplification, [status(thm)], [c_28, c_26, c_24, c_26, c_145])).
% 2.33/1.30  tff(c_174, plain, ('#skF_5'('#skF_7', '#skF_8', '#skF_9', '#skF_11')='#skF_10'), inference(resolution, [status(thm)], [c_32, c_150])).
% 2.33/1.30  tff(c_14, plain, (![A_65, B_66, C_67, D_83]: (k3_mcart_1('#skF_4'(A_65, B_66, C_67, D_83), '#skF_5'(A_65, B_66, C_67, D_83), '#skF_6'(A_65, B_66, C_67, D_83))=D_83 | ~m1_subset_1(D_83, k3_zfmisc_1(A_65, B_66, C_67)) | k1_xboole_0=C_67 | k1_xboole_0=B_66 | k1_xboole_0=A_65)), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.33/1.30  tff(c_181, plain, (k3_mcart_1('#skF_4'('#skF_7', '#skF_8', '#skF_9', '#skF_11'), '#skF_10', '#skF_6'('#skF_7', '#skF_8', '#skF_9', '#skF_11'))='#skF_11' | ~m1_subset_1('#skF_11', k3_zfmisc_1('#skF_7', '#skF_8', '#skF_9')) | k1_xboole_0='#skF_9' | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7'), inference(superposition, [status(thm), theory('equality')], [c_174, c_14])).
% 2.33/1.30  tff(c_192, plain, (k3_mcart_1('#skF_4'('#skF_7', '#skF_8', '#skF_9', '#skF_11'), '#skF_10', '#skF_6'('#skF_7', '#skF_8', '#skF_9', '#skF_11'))='#skF_11' | k1_xboole_0='#skF_9' | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_32, c_181])).
% 2.33/1.30  tff(c_193, plain, (k3_mcart_1('#skF_4'('#skF_7', '#skF_8', '#skF_9', '#skF_11'), '#skF_10', '#skF_6'('#skF_7', '#skF_8', '#skF_9', '#skF_11'))='#skF_11'), inference(negUnitSimplification, [status(thm)], [c_28, c_26, c_24, c_192])).
% 2.33/1.30  tff(c_12, plain, (![A_61, B_62, C_63, D_64]: (m1_subset_1(k6_mcart_1(A_61, B_62, C_63, D_64), B_62) | ~m1_subset_1(D_64, k3_zfmisc_1(A_61, B_62, C_63)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.33/1.30  tff(c_198, plain, (![B_166, G_165, H_170, C_167, A_168, F_169]: (k6_mcart_1(A_168, B_166, C_167, k3_mcart_1(F_169, G_165, H_170))=G_165 | ~m1_subset_1(k6_mcart_1(A_168, B_166, C_167, k3_mcart_1(F_169, G_165, H_170)), B_166) | ~m1_subset_1(k3_mcart_1(F_169, G_165, H_170), k3_zfmisc_1(A_168, B_166, C_167)) | k1_xboole_0=C_167 | k1_xboole_0=B_166 | k1_xboole_0=A_168)), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.33/1.30  tff(c_227, plain, (![H_171, G_172, B_174, C_173, A_175, F_176]: (k6_mcart_1(A_175, B_174, C_173, k3_mcart_1(F_176, G_172, H_171))=G_172 | k1_xboole_0=C_173 | k1_xboole_0=B_174 | k1_xboole_0=A_175 | ~m1_subset_1(k3_mcart_1(F_176, G_172, H_171), k3_zfmisc_1(A_175, B_174, C_173)))), inference(resolution, [status(thm)], [c_12, c_198])).
% 2.33/1.30  tff(c_230, plain, (![A_175, B_174, C_173]: (k6_mcart_1(A_175, B_174, C_173, k3_mcart_1('#skF_4'('#skF_7', '#skF_8', '#skF_9', '#skF_11'), '#skF_10', '#skF_6'('#skF_7', '#skF_8', '#skF_9', '#skF_11')))='#skF_10' | k1_xboole_0=C_173 | k1_xboole_0=B_174 | k1_xboole_0=A_175 | ~m1_subset_1('#skF_11', k3_zfmisc_1(A_175, B_174, C_173)))), inference(superposition, [status(thm), theory('equality')], [c_193, c_227])).
% 2.33/1.30  tff(c_242, plain, (![A_177, B_178, C_179]: (k6_mcart_1(A_177, B_178, C_179, '#skF_11')='#skF_10' | k1_xboole_0=C_179 | k1_xboole_0=B_178 | k1_xboole_0=A_177 | ~m1_subset_1('#skF_11', k3_zfmisc_1(A_177, B_178, C_179)))), inference(demodulation, [status(thm), theory('equality')], [c_193, c_230])).
% 2.33/1.30  tff(c_248, plain, (k6_mcart_1('#skF_7', '#skF_8', '#skF_9', '#skF_11')='#skF_10' | k1_xboole_0='#skF_9' | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7'), inference(resolution, [status(thm)], [c_32, c_242])).
% 2.33/1.30  tff(c_252, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28, c_26, c_24, c_22, c_248])).
% 2.33/1.30  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.33/1.30  
% 2.33/1.30  Inference rules
% 2.33/1.30  ----------------------
% 2.33/1.30  #Ref     : 0
% 2.33/1.30  #Sup     : 47
% 2.33/1.30  #Fact    : 0
% 2.33/1.30  #Define  : 0
% 2.33/1.30  #Split   : 0
% 2.33/1.30  #Chain   : 0
% 2.33/1.30  #Close   : 0
% 2.33/1.30  
% 2.33/1.30  Ordering : KBO
% 2.33/1.30  
% 2.33/1.30  Simplification rules
% 2.33/1.30  ----------------------
% 2.33/1.30  #Subsume      : 2
% 2.33/1.30  #Demod        : 19
% 2.33/1.30  #Tautology    : 20
% 2.33/1.30  #SimpNegUnit  : 7
% 2.33/1.30  #BackRed      : 0
% 2.33/1.30  
% 2.33/1.30  #Partial instantiations: 0
% 2.33/1.30  #Strategies tried      : 1
% 2.33/1.30  
% 2.33/1.30  Timing (in seconds)
% 2.33/1.30  ----------------------
% 2.33/1.31  Preprocessing        : 0.32
% 2.33/1.31  Parsing              : 0.17
% 2.33/1.31  CNF conversion       : 0.03
% 2.33/1.31  Main loop            : 0.22
% 2.33/1.31  Inferencing          : 0.08
% 2.33/1.31  Reduction            : 0.06
% 2.33/1.31  Demodulation         : 0.05
% 2.33/1.31  BG Simplification    : 0.02
% 2.33/1.31  Subsumption          : 0.04
% 2.33/1.31  Abstraction          : 0.01
% 2.33/1.31  MUC search           : 0.00
% 2.33/1.31  Cooper               : 0.00
% 2.33/1.31  Total                : 0.57
% 2.33/1.31  Index Insertion      : 0.00
% 2.33/1.31  Index Deletion       : 0.00
% 2.33/1.31  Index Matching       : 0.00
% 2.33/1.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
