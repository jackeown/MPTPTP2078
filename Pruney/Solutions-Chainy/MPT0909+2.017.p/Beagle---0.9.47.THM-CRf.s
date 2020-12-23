%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:59 EST 2020

% Result     : Theorem 2.38s
% Output     : CNFRefutation 2.38s
% Verified   : 
% Statistics : Number of formulae       :   52 ( 140 expanded)
%              Number of leaves         :   23 (  66 expanded)
%              Depth                    :   16
%              Number of atoms          :  147 ( 673 expanded)
%              Number of equality atoms :   98 ( 420 expanded)
%              Maximal formula depth    :   18 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_subset_1 > k5_mcart_1 > k3_zfmisc_1 > k3_mcart_1 > #nlpp > k1_xboole_0 > #skF_11 > #skF_2 > #skF_7 > #skF_10 > #skF_6 > #skF_9 > #skF_4 > #skF_3 > #skF_1 > #skF_8 > #skF_5

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff('#skF_11',type,(
    '#skF_11': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i * $i ) > $i )).

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

tff(k5_mcart_1,type,(
    k5_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_102,negated_conjecture,(
    ~ ! [A,B,C,D,E] :
        ( m1_subset_1(E,k3_zfmisc_1(A,B,C))
       => ( ! [F] :
              ( m1_subset_1(F,A)
             => ! [G] :
                  ( m1_subset_1(G,B)
                 => ! [H] :
                      ( m1_subset_1(H,C)
                     => ( E = k3_mcart_1(F,G,H)
                       => D = F ) ) ) )
         => ( A = k1_xboole_0
            | B = k1_xboole_0
            | C = k1_xboole_0
            | D = k5_mcart_1(A,B,C,E) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_mcart_1)).

tff(f_78,axiom,(
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

tff(f_53,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k3_zfmisc_1(A,B,C))
     => m1_subset_1(k5_mcart_1(A,B,C,D),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_mcart_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & C != k1_xboole_0
        & ~ ! [D] :
              ( m1_subset_1(D,k3_zfmisc_1(A,B,C))
             => ! [E] :
                  ( m1_subset_1(E,A)
                 => ( E = k5_mcart_1(A,B,C,D)
                  <=> ! [F,G,H] :
                        ( D = k3_mcart_1(F,G,H)
                       => E = F ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_mcart_1)).

tff(c_24,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_22,plain,(
    k1_xboole_0 != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_20,plain,(
    k1_xboole_0 != '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_18,plain,(
    k5_mcart_1('#skF_7','#skF_8','#skF_9','#skF_11') != '#skF_10' ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_28,plain,(
    m1_subset_1('#skF_11',k3_zfmisc_1('#skF_7','#skF_8','#skF_9')) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_14,plain,(
    ! [A_59,B_60,C_61,D_77] :
      ( m1_subset_1('#skF_5'(A_59,B_60,C_61,D_77),B_60)
      | ~ m1_subset_1(D_77,k3_zfmisc_1(A_59,B_60,C_61))
      | k1_xboole_0 = C_61
      | k1_xboole_0 = B_60
      | k1_xboole_0 = A_59 ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_16,plain,(
    ! [A_59,B_60,C_61,D_77] :
      ( m1_subset_1('#skF_4'(A_59,B_60,C_61,D_77),A_59)
      | ~ m1_subset_1(D_77,k3_zfmisc_1(A_59,B_60,C_61))
      | k1_xboole_0 = C_61
      | k1_xboole_0 = B_60
      | k1_xboole_0 = A_59 ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_12,plain,(
    ! [A_59,B_60,C_61,D_77] :
      ( m1_subset_1('#skF_6'(A_59,B_60,C_61,D_77),C_61)
      | ~ m1_subset_1(D_77,k3_zfmisc_1(A_59,B_60,C_61))
      | k1_xboole_0 = C_61
      | k1_xboole_0 = B_60
      | k1_xboole_0 = A_59 ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_41,plain,(
    ! [A_127,B_128,C_129,D_130] :
      ( k3_mcart_1('#skF_4'(A_127,B_128,C_129,D_130),'#skF_5'(A_127,B_128,C_129,D_130),'#skF_6'(A_127,B_128,C_129,D_130)) = D_130
      | ~ m1_subset_1(D_130,k3_zfmisc_1(A_127,B_128,C_129))
      | k1_xboole_0 = C_129
      | k1_xboole_0 = B_128
      | k1_xboole_0 = A_127 ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_26,plain,(
    ! [F_96,G_100,H_102] :
      ( F_96 = '#skF_10'
      | k3_mcart_1(F_96,G_100,H_102) != '#skF_11'
      | ~ m1_subset_1(H_102,'#skF_9')
      | ~ m1_subset_1(G_100,'#skF_8')
      | ~ m1_subset_1(F_96,'#skF_7') ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_87,plain,(
    ! [A_148,B_149,C_150,D_151] :
      ( '#skF_4'(A_148,B_149,C_150,D_151) = '#skF_10'
      | D_151 != '#skF_11'
      | ~ m1_subset_1('#skF_6'(A_148,B_149,C_150,D_151),'#skF_9')
      | ~ m1_subset_1('#skF_5'(A_148,B_149,C_150,D_151),'#skF_8')
      | ~ m1_subset_1('#skF_4'(A_148,B_149,C_150,D_151),'#skF_7')
      | ~ m1_subset_1(D_151,k3_zfmisc_1(A_148,B_149,C_150))
      | k1_xboole_0 = C_150
      | k1_xboole_0 = B_149
      | k1_xboole_0 = A_148 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_41,c_26])).

tff(c_91,plain,(
    ! [A_59,B_60,D_77] :
      ( '#skF_4'(A_59,B_60,'#skF_9',D_77) = '#skF_10'
      | D_77 != '#skF_11'
      | ~ m1_subset_1('#skF_5'(A_59,B_60,'#skF_9',D_77),'#skF_8')
      | ~ m1_subset_1('#skF_4'(A_59,B_60,'#skF_9',D_77),'#skF_7')
      | ~ m1_subset_1(D_77,k3_zfmisc_1(A_59,B_60,'#skF_9'))
      | k1_xboole_0 = '#skF_9'
      | k1_xboole_0 = B_60
      | k1_xboole_0 = A_59 ) ),
    inference(resolution,[status(thm)],[c_12,c_87])).

tff(c_96,plain,(
    ! [A_152,B_153,D_154] :
      ( '#skF_4'(A_152,B_153,'#skF_9',D_154) = '#skF_10'
      | D_154 != '#skF_11'
      | ~ m1_subset_1('#skF_5'(A_152,B_153,'#skF_9',D_154),'#skF_8')
      | ~ m1_subset_1('#skF_4'(A_152,B_153,'#skF_9',D_154),'#skF_7')
      | ~ m1_subset_1(D_154,k3_zfmisc_1(A_152,B_153,'#skF_9'))
      | k1_xboole_0 = B_153
      | k1_xboole_0 = A_152 ) ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_20,c_91])).

tff(c_100,plain,(
    ! [B_60,D_77] :
      ( '#skF_4'('#skF_7',B_60,'#skF_9',D_77) = '#skF_10'
      | D_77 != '#skF_11'
      | ~ m1_subset_1('#skF_5'('#skF_7',B_60,'#skF_9',D_77),'#skF_8')
      | ~ m1_subset_1(D_77,k3_zfmisc_1('#skF_7',B_60,'#skF_9'))
      | k1_xboole_0 = '#skF_9'
      | k1_xboole_0 = B_60
      | k1_xboole_0 = '#skF_7' ) ),
    inference(resolution,[status(thm)],[c_16,c_96])).

tff(c_105,plain,(
    ! [B_155,D_156] :
      ( '#skF_4'('#skF_7',B_155,'#skF_9',D_156) = '#skF_10'
      | D_156 != '#skF_11'
      | ~ m1_subset_1('#skF_5'('#skF_7',B_155,'#skF_9',D_156),'#skF_8')
      | ~ m1_subset_1(D_156,k3_zfmisc_1('#skF_7',B_155,'#skF_9'))
      | k1_xboole_0 = B_155 ) ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_20,c_24,c_100])).

tff(c_109,plain,(
    ! [D_77] :
      ( '#skF_4'('#skF_7','#skF_8','#skF_9',D_77) = '#skF_10'
      | D_77 != '#skF_11'
      | ~ m1_subset_1(D_77,k3_zfmisc_1('#skF_7','#skF_8','#skF_9'))
      | k1_xboole_0 = '#skF_9'
      | k1_xboole_0 = '#skF_8'
      | k1_xboole_0 = '#skF_7' ) ),
    inference(resolution,[status(thm)],[c_14,c_105])).

tff(c_114,plain,(
    ! [D_157] :
      ( '#skF_4'('#skF_7','#skF_8','#skF_9',D_157) = '#skF_10'
      | D_157 != '#skF_11'
      | ~ m1_subset_1(D_157,k3_zfmisc_1('#skF_7','#skF_8','#skF_9')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_22,c_20,c_22,c_109])).

tff(c_138,plain,(
    '#skF_4'('#skF_7','#skF_8','#skF_9','#skF_11') = '#skF_10' ),
    inference(resolution,[status(thm)],[c_28,c_114])).

tff(c_10,plain,(
    ! [A_59,B_60,C_61,D_77] :
      ( k3_mcart_1('#skF_4'(A_59,B_60,C_61,D_77),'#skF_5'(A_59,B_60,C_61,D_77),'#skF_6'(A_59,B_60,C_61,D_77)) = D_77
      | ~ m1_subset_1(D_77,k3_zfmisc_1(A_59,B_60,C_61))
      | k1_xboole_0 = C_61
      | k1_xboole_0 = B_60
      | k1_xboole_0 = A_59 ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_145,plain,
    ( k3_mcart_1('#skF_10','#skF_5'('#skF_7','#skF_8','#skF_9','#skF_11'),'#skF_6'('#skF_7','#skF_8','#skF_9','#skF_11')) = '#skF_11'
    | ~ m1_subset_1('#skF_11',k3_zfmisc_1('#skF_7','#skF_8','#skF_9'))
    | k1_xboole_0 = '#skF_9'
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7' ),
    inference(superposition,[status(thm),theory(equality)],[c_138,c_10])).

tff(c_156,plain,
    ( k3_mcart_1('#skF_10','#skF_5'('#skF_7','#skF_8','#skF_9','#skF_11'),'#skF_6'('#skF_7','#skF_8','#skF_9','#skF_11')) = '#skF_11'
    | k1_xboole_0 = '#skF_9'
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_145])).

tff(c_157,plain,(
    k3_mcart_1('#skF_10','#skF_5'('#skF_7','#skF_8','#skF_9','#skF_11'),'#skF_6'('#skF_7','#skF_8','#skF_9','#skF_11')) = '#skF_11' ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_22,c_20,c_156])).

tff(c_8,plain,(
    ! [A_55,B_56,C_57,D_58] :
      ( m1_subset_1(k5_mcart_1(A_55,B_56,C_57,D_58),A_55)
      | ~ m1_subset_1(D_58,k3_zfmisc_1(A_55,B_56,C_57)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_52,plain,(
    ! [H_133,G_131,A_136,F_132,B_134,C_135] :
      ( k5_mcart_1(A_136,B_134,C_135,k3_mcart_1(F_132,G_131,H_133)) = F_132
      | ~ m1_subset_1(k5_mcart_1(A_136,B_134,C_135,k3_mcart_1(F_132,G_131,H_133)),A_136)
      | ~ m1_subset_1(k3_mcart_1(F_132,G_131,H_133),k3_zfmisc_1(A_136,B_134,C_135))
      | k1_xboole_0 = C_135
      | k1_xboole_0 = B_134
      | k1_xboole_0 = A_136 ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_60,plain,(
    ! [B_56,C_57,H_133,G_131,F_132,A_55] :
      ( k5_mcart_1(A_55,B_56,C_57,k3_mcart_1(F_132,G_131,H_133)) = F_132
      | k1_xboole_0 = C_57
      | k1_xboole_0 = B_56
      | k1_xboole_0 = A_55
      | ~ m1_subset_1(k3_mcart_1(F_132,G_131,H_133),k3_zfmisc_1(A_55,B_56,C_57)) ) ),
    inference(resolution,[status(thm)],[c_8,c_52])).

tff(c_165,plain,(
    ! [A_55,B_56,C_57] :
      ( k5_mcart_1(A_55,B_56,C_57,k3_mcart_1('#skF_10','#skF_5'('#skF_7','#skF_8','#skF_9','#skF_11'),'#skF_6'('#skF_7','#skF_8','#skF_9','#skF_11'))) = '#skF_10'
      | k1_xboole_0 = C_57
      | k1_xboole_0 = B_56
      | k1_xboole_0 = A_55
      | ~ m1_subset_1('#skF_11',k3_zfmisc_1(A_55,B_56,C_57)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_157,c_60])).

tff(c_176,plain,(
    ! [A_158,B_159,C_160] :
      ( k5_mcart_1(A_158,B_159,C_160,'#skF_11') = '#skF_10'
      | k1_xboole_0 = C_160
      | k1_xboole_0 = B_159
      | k1_xboole_0 = A_158
      | ~ m1_subset_1('#skF_11',k3_zfmisc_1(A_158,B_159,C_160)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_157,c_165])).

tff(c_179,plain,
    ( k5_mcart_1('#skF_7','#skF_8','#skF_9','#skF_11') = '#skF_10'
    | k1_xboole_0 = '#skF_9'
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7' ),
    inference(resolution,[status(thm)],[c_28,c_176])).

tff(c_183,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_22,c_20,c_18,c_179])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:41:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.38/1.26  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.38/1.27  
% 2.38/1.27  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.38/1.27  %$ m1_subset_1 > k5_mcart_1 > k3_zfmisc_1 > k3_mcart_1 > #nlpp > k1_xboole_0 > #skF_11 > #skF_2 > #skF_7 > #skF_10 > #skF_6 > #skF_9 > #skF_4 > #skF_3 > #skF_1 > #skF_8 > #skF_5
% 2.38/1.27  
% 2.38/1.27  %Foreground sorts:
% 2.38/1.27  
% 2.38/1.27  
% 2.38/1.27  %Background operators:
% 2.38/1.27  
% 2.38/1.27  
% 2.38/1.27  %Foreground operators:
% 2.38/1.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.38/1.27  tff('#skF_11', type, '#skF_11': $i).
% 2.38/1.27  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i * $i) > $i).
% 2.38/1.27  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.38/1.27  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 2.38/1.27  tff('#skF_7', type, '#skF_7': $i).
% 2.38/1.27  tff('#skF_10', type, '#skF_10': $i).
% 2.38/1.27  tff('#skF_6', type, '#skF_6': ($i * $i * $i * $i) > $i).
% 2.38/1.27  tff('#skF_9', type, '#skF_9': $i).
% 2.38/1.27  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 2.38/1.27  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 2.38/1.27  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i * $i) > $i).
% 2.38/1.27  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i * $i) > $i).
% 2.38/1.27  tff('#skF_8', type, '#skF_8': $i).
% 2.38/1.27  tff(k5_mcart_1, type, k5_mcart_1: ($i * $i * $i * $i) > $i).
% 2.38/1.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.38/1.27  tff('#skF_5', type, '#skF_5': ($i * $i * $i * $i) > $i).
% 2.38/1.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.38/1.27  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.38/1.27  
% 2.38/1.29  tff(f_102, negated_conjecture, ~(![A, B, C, D, E]: (m1_subset_1(E, k3_zfmisc_1(A, B, C)) => ((![F]: (m1_subset_1(F, A) => (![G]: (m1_subset_1(G, B) => (![H]: (m1_subset_1(H, C) => ((E = k3_mcart_1(F, G, H)) => (D = F)))))))) => ((((A = k1_xboole_0) | (B = k1_xboole_0)) | (C = k1_xboole_0)) | (D = k5_mcart_1(A, B, C, E)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_mcart_1)).
% 2.38/1.29  tff(f_78, axiom, (![A, B, C]: ~(((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & (?[D]: (m1_subset_1(D, k3_zfmisc_1(A, B, C)) & (![E]: (m1_subset_1(E, A) => (![F]: (m1_subset_1(F, B) => (![G]: (m1_subset_1(G, C) => ~(D = k3_mcart_1(E, F, G)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l44_mcart_1)).
% 2.38/1.29  tff(f_53, axiom, (![A, B, C, D]: (m1_subset_1(D, k3_zfmisc_1(A, B, C)) => m1_subset_1(k5_mcart_1(A, B, C, D), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k5_mcart_1)).
% 2.38/1.29  tff(f_49, axiom, (![A, B, C]: ~(((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(![D]: (m1_subset_1(D, k3_zfmisc_1(A, B, C)) => (![E]: (m1_subset_1(E, A) => ((E = k5_mcart_1(A, B, C, D)) <=> (![F, G, H]: ((D = k3_mcart_1(F, G, H)) => (E = F)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_mcart_1)).
% 2.38/1.29  tff(c_24, plain, (k1_xboole_0!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.38/1.29  tff(c_22, plain, (k1_xboole_0!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.38/1.29  tff(c_20, plain, (k1_xboole_0!='#skF_9'), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.38/1.29  tff(c_18, plain, (k5_mcart_1('#skF_7', '#skF_8', '#skF_9', '#skF_11')!='#skF_10'), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.38/1.29  tff(c_28, plain, (m1_subset_1('#skF_11', k3_zfmisc_1('#skF_7', '#skF_8', '#skF_9'))), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.38/1.29  tff(c_14, plain, (![A_59, B_60, C_61, D_77]: (m1_subset_1('#skF_5'(A_59, B_60, C_61, D_77), B_60) | ~m1_subset_1(D_77, k3_zfmisc_1(A_59, B_60, C_61)) | k1_xboole_0=C_61 | k1_xboole_0=B_60 | k1_xboole_0=A_59)), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.38/1.29  tff(c_16, plain, (![A_59, B_60, C_61, D_77]: (m1_subset_1('#skF_4'(A_59, B_60, C_61, D_77), A_59) | ~m1_subset_1(D_77, k3_zfmisc_1(A_59, B_60, C_61)) | k1_xboole_0=C_61 | k1_xboole_0=B_60 | k1_xboole_0=A_59)), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.38/1.29  tff(c_12, plain, (![A_59, B_60, C_61, D_77]: (m1_subset_1('#skF_6'(A_59, B_60, C_61, D_77), C_61) | ~m1_subset_1(D_77, k3_zfmisc_1(A_59, B_60, C_61)) | k1_xboole_0=C_61 | k1_xboole_0=B_60 | k1_xboole_0=A_59)), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.38/1.29  tff(c_41, plain, (![A_127, B_128, C_129, D_130]: (k3_mcart_1('#skF_4'(A_127, B_128, C_129, D_130), '#skF_5'(A_127, B_128, C_129, D_130), '#skF_6'(A_127, B_128, C_129, D_130))=D_130 | ~m1_subset_1(D_130, k3_zfmisc_1(A_127, B_128, C_129)) | k1_xboole_0=C_129 | k1_xboole_0=B_128 | k1_xboole_0=A_127)), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.38/1.29  tff(c_26, plain, (![F_96, G_100, H_102]: (F_96='#skF_10' | k3_mcart_1(F_96, G_100, H_102)!='#skF_11' | ~m1_subset_1(H_102, '#skF_9') | ~m1_subset_1(G_100, '#skF_8') | ~m1_subset_1(F_96, '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.38/1.29  tff(c_87, plain, (![A_148, B_149, C_150, D_151]: ('#skF_4'(A_148, B_149, C_150, D_151)='#skF_10' | D_151!='#skF_11' | ~m1_subset_1('#skF_6'(A_148, B_149, C_150, D_151), '#skF_9') | ~m1_subset_1('#skF_5'(A_148, B_149, C_150, D_151), '#skF_8') | ~m1_subset_1('#skF_4'(A_148, B_149, C_150, D_151), '#skF_7') | ~m1_subset_1(D_151, k3_zfmisc_1(A_148, B_149, C_150)) | k1_xboole_0=C_150 | k1_xboole_0=B_149 | k1_xboole_0=A_148)), inference(superposition, [status(thm), theory('equality')], [c_41, c_26])).
% 2.38/1.29  tff(c_91, plain, (![A_59, B_60, D_77]: ('#skF_4'(A_59, B_60, '#skF_9', D_77)='#skF_10' | D_77!='#skF_11' | ~m1_subset_1('#skF_5'(A_59, B_60, '#skF_9', D_77), '#skF_8') | ~m1_subset_1('#skF_4'(A_59, B_60, '#skF_9', D_77), '#skF_7') | ~m1_subset_1(D_77, k3_zfmisc_1(A_59, B_60, '#skF_9')) | k1_xboole_0='#skF_9' | k1_xboole_0=B_60 | k1_xboole_0=A_59)), inference(resolution, [status(thm)], [c_12, c_87])).
% 2.38/1.29  tff(c_96, plain, (![A_152, B_153, D_154]: ('#skF_4'(A_152, B_153, '#skF_9', D_154)='#skF_10' | D_154!='#skF_11' | ~m1_subset_1('#skF_5'(A_152, B_153, '#skF_9', D_154), '#skF_8') | ~m1_subset_1('#skF_4'(A_152, B_153, '#skF_9', D_154), '#skF_7') | ~m1_subset_1(D_154, k3_zfmisc_1(A_152, B_153, '#skF_9')) | k1_xboole_0=B_153 | k1_xboole_0=A_152)), inference(negUnitSimplification, [status(thm)], [c_20, c_20, c_91])).
% 2.38/1.29  tff(c_100, plain, (![B_60, D_77]: ('#skF_4'('#skF_7', B_60, '#skF_9', D_77)='#skF_10' | D_77!='#skF_11' | ~m1_subset_1('#skF_5'('#skF_7', B_60, '#skF_9', D_77), '#skF_8') | ~m1_subset_1(D_77, k3_zfmisc_1('#skF_7', B_60, '#skF_9')) | k1_xboole_0='#skF_9' | k1_xboole_0=B_60 | k1_xboole_0='#skF_7')), inference(resolution, [status(thm)], [c_16, c_96])).
% 2.38/1.29  tff(c_105, plain, (![B_155, D_156]: ('#skF_4'('#skF_7', B_155, '#skF_9', D_156)='#skF_10' | D_156!='#skF_11' | ~m1_subset_1('#skF_5'('#skF_7', B_155, '#skF_9', D_156), '#skF_8') | ~m1_subset_1(D_156, k3_zfmisc_1('#skF_7', B_155, '#skF_9')) | k1_xboole_0=B_155)), inference(negUnitSimplification, [status(thm)], [c_24, c_20, c_24, c_100])).
% 2.38/1.29  tff(c_109, plain, (![D_77]: ('#skF_4'('#skF_7', '#skF_8', '#skF_9', D_77)='#skF_10' | D_77!='#skF_11' | ~m1_subset_1(D_77, k3_zfmisc_1('#skF_7', '#skF_8', '#skF_9')) | k1_xboole_0='#skF_9' | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7')), inference(resolution, [status(thm)], [c_14, c_105])).
% 2.38/1.29  tff(c_114, plain, (![D_157]: ('#skF_4'('#skF_7', '#skF_8', '#skF_9', D_157)='#skF_10' | D_157!='#skF_11' | ~m1_subset_1(D_157, k3_zfmisc_1('#skF_7', '#skF_8', '#skF_9')))), inference(negUnitSimplification, [status(thm)], [c_24, c_22, c_20, c_22, c_109])).
% 2.38/1.29  tff(c_138, plain, ('#skF_4'('#skF_7', '#skF_8', '#skF_9', '#skF_11')='#skF_10'), inference(resolution, [status(thm)], [c_28, c_114])).
% 2.38/1.29  tff(c_10, plain, (![A_59, B_60, C_61, D_77]: (k3_mcart_1('#skF_4'(A_59, B_60, C_61, D_77), '#skF_5'(A_59, B_60, C_61, D_77), '#skF_6'(A_59, B_60, C_61, D_77))=D_77 | ~m1_subset_1(D_77, k3_zfmisc_1(A_59, B_60, C_61)) | k1_xboole_0=C_61 | k1_xboole_0=B_60 | k1_xboole_0=A_59)), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.38/1.29  tff(c_145, plain, (k3_mcart_1('#skF_10', '#skF_5'('#skF_7', '#skF_8', '#skF_9', '#skF_11'), '#skF_6'('#skF_7', '#skF_8', '#skF_9', '#skF_11'))='#skF_11' | ~m1_subset_1('#skF_11', k3_zfmisc_1('#skF_7', '#skF_8', '#skF_9')) | k1_xboole_0='#skF_9' | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7'), inference(superposition, [status(thm), theory('equality')], [c_138, c_10])).
% 2.38/1.29  tff(c_156, plain, (k3_mcart_1('#skF_10', '#skF_5'('#skF_7', '#skF_8', '#skF_9', '#skF_11'), '#skF_6'('#skF_7', '#skF_8', '#skF_9', '#skF_11'))='#skF_11' | k1_xboole_0='#skF_9' | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_28, c_145])).
% 2.38/1.29  tff(c_157, plain, (k3_mcart_1('#skF_10', '#skF_5'('#skF_7', '#skF_8', '#skF_9', '#skF_11'), '#skF_6'('#skF_7', '#skF_8', '#skF_9', '#skF_11'))='#skF_11'), inference(negUnitSimplification, [status(thm)], [c_24, c_22, c_20, c_156])).
% 2.38/1.29  tff(c_8, plain, (![A_55, B_56, C_57, D_58]: (m1_subset_1(k5_mcart_1(A_55, B_56, C_57, D_58), A_55) | ~m1_subset_1(D_58, k3_zfmisc_1(A_55, B_56, C_57)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.38/1.29  tff(c_52, plain, (![H_133, G_131, A_136, F_132, B_134, C_135]: (k5_mcart_1(A_136, B_134, C_135, k3_mcart_1(F_132, G_131, H_133))=F_132 | ~m1_subset_1(k5_mcart_1(A_136, B_134, C_135, k3_mcart_1(F_132, G_131, H_133)), A_136) | ~m1_subset_1(k3_mcart_1(F_132, G_131, H_133), k3_zfmisc_1(A_136, B_134, C_135)) | k1_xboole_0=C_135 | k1_xboole_0=B_134 | k1_xboole_0=A_136)), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.38/1.29  tff(c_60, plain, (![B_56, C_57, H_133, G_131, F_132, A_55]: (k5_mcart_1(A_55, B_56, C_57, k3_mcart_1(F_132, G_131, H_133))=F_132 | k1_xboole_0=C_57 | k1_xboole_0=B_56 | k1_xboole_0=A_55 | ~m1_subset_1(k3_mcart_1(F_132, G_131, H_133), k3_zfmisc_1(A_55, B_56, C_57)))), inference(resolution, [status(thm)], [c_8, c_52])).
% 2.38/1.29  tff(c_165, plain, (![A_55, B_56, C_57]: (k5_mcart_1(A_55, B_56, C_57, k3_mcart_1('#skF_10', '#skF_5'('#skF_7', '#skF_8', '#skF_9', '#skF_11'), '#skF_6'('#skF_7', '#skF_8', '#skF_9', '#skF_11')))='#skF_10' | k1_xboole_0=C_57 | k1_xboole_0=B_56 | k1_xboole_0=A_55 | ~m1_subset_1('#skF_11', k3_zfmisc_1(A_55, B_56, C_57)))), inference(superposition, [status(thm), theory('equality')], [c_157, c_60])).
% 2.38/1.29  tff(c_176, plain, (![A_158, B_159, C_160]: (k5_mcart_1(A_158, B_159, C_160, '#skF_11')='#skF_10' | k1_xboole_0=C_160 | k1_xboole_0=B_159 | k1_xboole_0=A_158 | ~m1_subset_1('#skF_11', k3_zfmisc_1(A_158, B_159, C_160)))), inference(demodulation, [status(thm), theory('equality')], [c_157, c_165])).
% 2.38/1.29  tff(c_179, plain, (k5_mcart_1('#skF_7', '#skF_8', '#skF_9', '#skF_11')='#skF_10' | k1_xboole_0='#skF_9' | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7'), inference(resolution, [status(thm)], [c_28, c_176])).
% 2.38/1.29  tff(c_183, plain, $false, inference(negUnitSimplification, [status(thm)], [c_24, c_22, c_20, c_18, c_179])).
% 2.38/1.29  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.38/1.29  
% 2.38/1.29  Inference rules
% 2.38/1.29  ----------------------
% 2.38/1.29  #Ref     : 0
% 2.38/1.29  #Sup     : 28
% 2.38/1.29  #Fact    : 0
% 2.38/1.29  #Define  : 0
% 2.38/1.29  #Split   : 0
% 2.38/1.29  #Chain   : 0
% 2.38/1.29  #Close   : 0
% 2.38/1.29  
% 2.38/1.29  Ordering : KBO
% 2.38/1.29  
% 2.38/1.29  Simplification rules
% 2.38/1.29  ----------------------
% 2.38/1.29  #Subsume      : 1
% 2.38/1.29  #Demod        : 6
% 2.38/1.29  #Tautology    : 10
% 2.38/1.29  #SimpNegUnit  : 7
% 2.38/1.29  #BackRed      : 0
% 2.38/1.29  
% 2.38/1.29  #Partial instantiations: 0
% 2.38/1.29  #Strategies tried      : 1
% 2.38/1.29  
% 2.38/1.29  Timing (in seconds)
% 2.38/1.29  ----------------------
% 2.38/1.29  Preprocessing        : 0.32
% 2.38/1.29  Parsing              : 0.16
% 2.38/1.29  CNF conversion       : 0.03
% 2.38/1.29  Main loop            : 0.20
% 2.38/1.29  Inferencing          : 0.09
% 2.38/1.29  Reduction            : 0.05
% 2.38/1.29  Demodulation         : 0.03
% 2.38/1.29  BG Simplification    : 0.02
% 2.38/1.29  Subsumption          : 0.04
% 2.38/1.29  Abstraction          : 0.01
% 2.38/1.29  MUC search           : 0.00
% 2.38/1.29  Cooper               : 0.00
% 2.38/1.29  Total                : 0.55
% 2.38/1.29  Index Insertion      : 0.00
% 2.38/1.29  Index Deletion       : 0.00
% 2.38/1.29  Index Matching       : 0.00
% 2.38/1.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------
