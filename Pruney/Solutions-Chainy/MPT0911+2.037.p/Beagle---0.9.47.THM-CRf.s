%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:06 EST 2020

% Result     : Theorem 2.44s
% Output     : CNFRefutation 2.44s
% Verified   : 
% Statistics : Number of formulae       :   50 ( 138 expanded)
%              Number of leaves         :   23 (  66 expanded)
%              Depth                    :   16
%              Number of atoms          :  137 ( 663 expanded)
%              Number of equality atoms :   95 ( 417 expanded)
%              Maximal formula depth    :   17 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_subset_1 > k7_mcart_1 > k6_mcart_1 > k5_mcart_1 > k3_zfmisc_1 > k3_mcart_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_7 > #skF_5 > #skF_2 > #skF_6 > #skF_8 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_mcart_1,type,(
    k3_mcart_1: ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k7_mcart_1,type,(
    k7_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff(k3_zfmisc_1,type,(
    k3_zfmisc_1: ( $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff(k5_mcart_1,type,(
    k5_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k6_mcart_1,type,(
    k6_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_101,negated_conjecture,(
    ~ ! [A,B,C,D,E] :
        ( m1_subset_1(E,k3_zfmisc_1(A,B,C))
       => ( ! [F] :
              ( m1_subset_1(F,A)
             => ! [G] :
                  ( m1_subset_1(G,B)
                 => ! [H] :
                      ( m1_subset_1(H,C)
                     => ( E = k3_mcart_1(F,G,H)
                       => D = H ) ) ) )
         => ( A = k1_xboole_0
            | B = k1_xboole_0
            | C = k1_xboole_0
            | D = k7_mcart_1(A,B,C,E) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_mcart_1)).

tff(f_54,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l44_mcart_1)).

tff(f_77,axiom,(
    ! [A,B,C] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & C != k1_xboole_0
        & ? [D] :
            ( m1_subset_1(D,k3_zfmisc_1(A,B,C))
            & ? [E,F,G] :
                ( D = k3_mcart_1(E,F,G)
                & ~ ( k5_mcart_1(A,B,C,D) = E
                    & k6_mcart_1(A,B,C,D) = F
                    & k7_mcart_1(A,B,C,D) = G ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_mcart_1)).

tff(c_26,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_24,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_22,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_20,plain,(
    k7_mcart_1('#skF_4','#skF_5','#skF_6','#skF_8') != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_30,plain,(
    m1_subset_1('#skF_8',k3_zfmisc_1('#skF_4','#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_12,plain,(
    ! [A_7,B_8,C_9,D_25] :
      ( m1_subset_1('#skF_1'(A_7,B_8,C_9,D_25),A_7)
      | ~ m1_subset_1(D_25,k3_zfmisc_1(A_7,B_8,C_9))
      | k1_xboole_0 = C_9
      | k1_xboole_0 = B_8
      | k1_xboole_0 = A_7 ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_8,plain,(
    ! [A_7,B_8,C_9,D_25] :
      ( m1_subset_1('#skF_3'(A_7,B_8,C_9,D_25),C_9)
      | ~ m1_subset_1(D_25,k3_zfmisc_1(A_7,B_8,C_9))
      | k1_xboole_0 = C_9
      | k1_xboole_0 = B_8
      | k1_xboole_0 = A_7 ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_10,plain,(
    ! [A_7,B_8,C_9,D_25] :
      ( m1_subset_1('#skF_2'(A_7,B_8,C_9,D_25),B_8)
      | ~ m1_subset_1(D_25,k3_zfmisc_1(A_7,B_8,C_9))
      | k1_xboole_0 = C_9
      | k1_xboole_0 = B_8
      | k1_xboole_0 = A_7 ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_129,plain,(
    ! [A_119,B_120,C_121,D_122] :
      ( k3_mcart_1('#skF_1'(A_119,B_120,C_121,D_122),'#skF_2'(A_119,B_120,C_121,D_122),'#skF_3'(A_119,B_120,C_121,D_122)) = D_122
      | ~ m1_subset_1(D_122,k3_zfmisc_1(A_119,B_120,C_121))
      | k1_xboole_0 = C_121
      | k1_xboole_0 = B_120
      | k1_xboole_0 = A_119 ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_28,plain,(
    ! [H_67,F_61,G_65] :
      ( H_67 = '#skF_7'
      | k3_mcart_1(F_61,G_65,H_67) != '#skF_8'
      | ~ m1_subset_1(H_67,'#skF_6')
      | ~ m1_subset_1(G_65,'#skF_5')
      | ~ m1_subset_1(F_61,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_210,plain,(
    ! [A_158,B_159,C_160,D_161] :
      ( '#skF_3'(A_158,B_159,C_160,D_161) = '#skF_7'
      | D_161 != '#skF_8'
      | ~ m1_subset_1('#skF_3'(A_158,B_159,C_160,D_161),'#skF_6')
      | ~ m1_subset_1('#skF_2'(A_158,B_159,C_160,D_161),'#skF_5')
      | ~ m1_subset_1('#skF_1'(A_158,B_159,C_160,D_161),'#skF_4')
      | ~ m1_subset_1(D_161,k3_zfmisc_1(A_158,B_159,C_160))
      | k1_xboole_0 = C_160
      | k1_xboole_0 = B_159
      | k1_xboole_0 = A_158 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_129,c_28])).

tff(c_214,plain,(
    ! [A_7,C_9,D_25] :
      ( '#skF_3'(A_7,'#skF_5',C_9,D_25) = '#skF_7'
      | D_25 != '#skF_8'
      | ~ m1_subset_1('#skF_3'(A_7,'#skF_5',C_9,D_25),'#skF_6')
      | ~ m1_subset_1('#skF_1'(A_7,'#skF_5',C_9,D_25),'#skF_4')
      | ~ m1_subset_1(D_25,k3_zfmisc_1(A_7,'#skF_5',C_9))
      | k1_xboole_0 = C_9
      | k1_xboole_0 = '#skF_5'
      | k1_xboole_0 = A_7 ) ),
    inference(resolution,[status(thm)],[c_10,c_210])).

tff(c_230,plain,(
    ! [A_169,C_170,D_171] :
      ( '#skF_3'(A_169,'#skF_5',C_170,D_171) = '#skF_7'
      | D_171 != '#skF_8'
      | ~ m1_subset_1('#skF_3'(A_169,'#skF_5',C_170,D_171),'#skF_6')
      | ~ m1_subset_1('#skF_1'(A_169,'#skF_5',C_170,D_171),'#skF_4')
      | ~ m1_subset_1(D_171,k3_zfmisc_1(A_169,'#skF_5',C_170))
      | k1_xboole_0 = C_170
      | k1_xboole_0 = A_169 ) ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_24,c_214])).

tff(c_234,plain,(
    ! [A_7,D_25] :
      ( '#skF_3'(A_7,'#skF_5','#skF_6',D_25) = '#skF_7'
      | D_25 != '#skF_8'
      | ~ m1_subset_1('#skF_1'(A_7,'#skF_5','#skF_6',D_25),'#skF_4')
      | ~ m1_subset_1(D_25,k3_zfmisc_1(A_7,'#skF_5','#skF_6'))
      | k1_xboole_0 = '#skF_6'
      | k1_xboole_0 = '#skF_5'
      | k1_xboole_0 = A_7 ) ),
    inference(resolution,[status(thm)],[c_8,c_230])).

tff(c_239,plain,(
    ! [A_172,D_173] :
      ( '#skF_3'(A_172,'#skF_5','#skF_6',D_173) = '#skF_7'
      | D_173 != '#skF_8'
      | ~ m1_subset_1('#skF_1'(A_172,'#skF_5','#skF_6',D_173),'#skF_4')
      | ~ m1_subset_1(D_173,k3_zfmisc_1(A_172,'#skF_5','#skF_6'))
      | k1_xboole_0 = A_172 ) ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_22,c_22,c_234])).

tff(c_243,plain,(
    ! [D_25] :
      ( '#skF_3'('#skF_4','#skF_5','#skF_6',D_25) = '#skF_7'
      | D_25 != '#skF_8'
      | ~ m1_subset_1(D_25,k3_zfmisc_1('#skF_4','#skF_5','#skF_6'))
      | k1_xboole_0 = '#skF_6'
      | k1_xboole_0 = '#skF_5'
      | k1_xboole_0 = '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_12,c_239])).

tff(c_248,plain,(
    ! [D_174] :
      ( '#skF_3'('#skF_4','#skF_5','#skF_6',D_174) = '#skF_7'
      | D_174 != '#skF_8'
      | ~ m1_subset_1(D_174,k3_zfmisc_1('#skF_4','#skF_5','#skF_6')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_24,c_22,c_26,c_243])).

tff(c_267,plain,(
    '#skF_3'('#skF_4','#skF_5','#skF_6','#skF_8') = '#skF_7' ),
    inference(resolution,[status(thm)],[c_30,c_248])).

tff(c_6,plain,(
    ! [A_7,B_8,C_9,D_25] :
      ( k3_mcart_1('#skF_1'(A_7,B_8,C_9,D_25),'#skF_2'(A_7,B_8,C_9,D_25),'#skF_3'(A_7,B_8,C_9,D_25)) = D_25
      | ~ m1_subset_1(D_25,k3_zfmisc_1(A_7,B_8,C_9))
      | k1_xboole_0 = C_9
      | k1_xboole_0 = B_8
      | k1_xboole_0 = A_7 ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_274,plain,
    ( k3_mcart_1('#skF_1'('#skF_4','#skF_5','#skF_6','#skF_8'),'#skF_2'('#skF_4','#skF_5','#skF_6','#skF_8'),'#skF_7') = '#skF_8'
    | ~ m1_subset_1('#skF_8',k3_zfmisc_1('#skF_4','#skF_5','#skF_6'))
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_267,c_6])).

tff(c_285,plain,
    ( k3_mcart_1('#skF_1'('#skF_4','#skF_5','#skF_6','#skF_8'),'#skF_2'('#skF_4','#skF_5','#skF_6','#skF_8'),'#skF_7') = '#skF_8'
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_274])).

tff(c_286,plain,(
    k3_mcart_1('#skF_1'('#skF_4','#skF_5','#skF_6','#skF_8'),'#skF_2'('#skF_4','#skF_5','#skF_6','#skF_8'),'#skF_7') = '#skF_8' ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_24,c_22,c_285])).

tff(c_14,plain,(
    ! [C_39,B_38,G_53,F_52,E_51,A_37] :
      ( k7_mcart_1(A_37,B_38,C_39,k3_mcart_1(E_51,F_52,G_53)) = G_53
      | ~ m1_subset_1(k3_mcart_1(E_51,F_52,G_53),k3_zfmisc_1(A_37,B_38,C_39))
      | k1_xboole_0 = C_39
      | k1_xboole_0 = B_38
      | k1_xboole_0 = A_37 ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_312,plain,(
    ! [A_37,B_38,C_39] :
      ( k7_mcart_1(A_37,B_38,C_39,k3_mcart_1('#skF_1'('#skF_4','#skF_5','#skF_6','#skF_8'),'#skF_2'('#skF_4','#skF_5','#skF_6','#skF_8'),'#skF_7')) = '#skF_7'
      | ~ m1_subset_1('#skF_8',k3_zfmisc_1(A_37,B_38,C_39))
      | k1_xboole_0 = C_39
      | k1_xboole_0 = B_38
      | k1_xboole_0 = A_37 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_286,c_14])).

tff(c_339,plain,(
    ! [A_175,B_176,C_177] :
      ( k7_mcart_1(A_175,B_176,C_177,'#skF_8') = '#skF_7'
      | ~ m1_subset_1('#skF_8',k3_zfmisc_1(A_175,B_176,C_177))
      | k1_xboole_0 = C_177
      | k1_xboole_0 = B_176
      | k1_xboole_0 = A_175 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_286,c_312])).

tff(c_345,plain,
    ( k7_mcart_1('#skF_4','#skF_5','#skF_6','#skF_8') = '#skF_7'
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_30,c_339])).

tff(c_349,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_24,c_22,c_20,c_345])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:38:05 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.44/1.36  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.44/1.37  
% 2.44/1.37  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.44/1.37  %$ m1_subset_1 > k7_mcart_1 > k6_mcart_1 > k5_mcart_1 > k3_zfmisc_1 > k3_mcart_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_7 > #skF_5 > #skF_2 > #skF_6 > #skF_8 > #skF_4 > #skF_3 > #skF_1
% 2.44/1.37  
% 2.44/1.37  %Foreground sorts:
% 2.44/1.37  
% 2.44/1.37  
% 2.44/1.37  %Background operators:
% 2.44/1.37  
% 2.44/1.37  
% 2.44/1.37  %Foreground operators:
% 2.44/1.37  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.44/1.37  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.44/1.37  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.44/1.37  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 2.44/1.37  tff('#skF_7', type, '#skF_7': $i).
% 2.44/1.37  tff('#skF_5', type, '#skF_5': $i).
% 2.44/1.37  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 2.44/1.37  tff('#skF_6', type, '#skF_6': $i).
% 2.44/1.37  tff(k7_mcart_1, type, k7_mcart_1: ($i * $i * $i * $i) > $i).
% 2.44/1.37  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 2.44/1.37  tff('#skF_8', type, '#skF_8': $i).
% 2.44/1.37  tff(k5_mcart_1, type, k5_mcart_1: ($i * $i * $i * $i) > $i).
% 2.44/1.37  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.44/1.37  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.44/1.37  tff('#skF_4', type, '#skF_4': $i).
% 2.44/1.37  tff(k6_mcart_1, type, k6_mcart_1: ($i * $i * $i * $i) > $i).
% 2.44/1.37  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.44/1.37  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 2.44/1.37  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 2.44/1.37  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.44/1.37  
% 2.44/1.38  tff(f_101, negated_conjecture, ~(![A, B, C, D, E]: (m1_subset_1(E, k3_zfmisc_1(A, B, C)) => ((![F]: (m1_subset_1(F, A) => (![G]: (m1_subset_1(G, B) => (![H]: (m1_subset_1(H, C) => ((E = k3_mcart_1(F, G, H)) => (D = H)))))))) => ((((A = k1_xboole_0) | (B = k1_xboole_0)) | (C = k1_xboole_0)) | (D = k7_mcart_1(A, B, C, E)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_mcart_1)).
% 2.44/1.38  tff(f_54, axiom, (![A, B, C]: ~(((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & (?[D]: (m1_subset_1(D, k3_zfmisc_1(A, B, C)) & (![E]: (m1_subset_1(E, A) => (![F]: (m1_subset_1(F, B) => (![G]: (m1_subset_1(G, C) => ~(D = k3_mcart_1(E, F, G)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l44_mcart_1)).
% 2.44/1.38  tff(f_77, axiom, (![A, B, C]: ~(((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & (?[D]: (m1_subset_1(D, k3_zfmisc_1(A, B, C)) & (?[E, F, G]: ((D = k3_mcart_1(E, F, G)) & ~(((k5_mcart_1(A, B, C, D) = E) & (k6_mcart_1(A, B, C, D) = F)) & (k7_mcart_1(A, B, C, D) = G)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_mcart_1)).
% 2.44/1.38  tff(c_26, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.44/1.38  tff(c_24, plain, (k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.44/1.38  tff(c_22, plain, (k1_xboole_0!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.44/1.38  tff(c_20, plain, (k7_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_8')!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.44/1.38  tff(c_30, plain, (m1_subset_1('#skF_8', k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.44/1.38  tff(c_12, plain, (![A_7, B_8, C_9, D_25]: (m1_subset_1('#skF_1'(A_7, B_8, C_9, D_25), A_7) | ~m1_subset_1(D_25, k3_zfmisc_1(A_7, B_8, C_9)) | k1_xboole_0=C_9 | k1_xboole_0=B_8 | k1_xboole_0=A_7)), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.44/1.38  tff(c_8, plain, (![A_7, B_8, C_9, D_25]: (m1_subset_1('#skF_3'(A_7, B_8, C_9, D_25), C_9) | ~m1_subset_1(D_25, k3_zfmisc_1(A_7, B_8, C_9)) | k1_xboole_0=C_9 | k1_xboole_0=B_8 | k1_xboole_0=A_7)), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.44/1.38  tff(c_10, plain, (![A_7, B_8, C_9, D_25]: (m1_subset_1('#skF_2'(A_7, B_8, C_9, D_25), B_8) | ~m1_subset_1(D_25, k3_zfmisc_1(A_7, B_8, C_9)) | k1_xboole_0=C_9 | k1_xboole_0=B_8 | k1_xboole_0=A_7)), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.44/1.38  tff(c_129, plain, (![A_119, B_120, C_121, D_122]: (k3_mcart_1('#skF_1'(A_119, B_120, C_121, D_122), '#skF_2'(A_119, B_120, C_121, D_122), '#skF_3'(A_119, B_120, C_121, D_122))=D_122 | ~m1_subset_1(D_122, k3_zfmisc_1(A_119, B_120, C_121)) | k1_xboole_0=C_121 | k1_xboole_0=B_120 | k1_xboole_0=A_119)), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.44/1.38  tff(c_28, plain, (![H_67, F_61, G_65]: (H_67='#skF_7' | k3_mcart_1(F_61, G_65, H_67)!='#skF_8' | ~m1_subset_1(H_67, '#skF_6') | ~m1_subset_1(G_65, '#skF_5') | ~m1_subset_1(F_61, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.44/1.38  tff(c_210, plain, (![A_158, B_159, C_160, D_161]: ('#skF_3'(A_158, B_159, C_160, D_161)='#skF_7' | D_161!='#skF_8' | ~m1_subset_1('#skF_3'(A_158, B_159, C_160, D_161), '#skF_6') | ~m1_subset_1('#skF_2'(A_158, B_159, C_160, D_161), '#skF_5') | ~m1_subset_1('#skF_1'(A_158, B_159, C_160, D_161), '#skF_4') | ~m1_subset_1(D_161, k3_zfmisc_1(A_158, B_159, C_160)) | k1_xboole_0=C_160 | k1_xboole_0=B_159 | k1_xboole_0=A_158)), inference(superposition, [status(thm), theory('equality')], [c_129, c_28])).
% 2.44/1.38  tff(c_214, plain, (![A_7, C_9, D_25]: ('#skF_3'(A_7, '#skF_5', C_9, D_25)='#skF_7' | D_25!='#skF_8' | ~m1_subset_1('#skF_3'(A_7, '#skF_5', C_9, D_25), '#skF_6') | ~m1_subset_1('#skF_1'(A_7, '#skF_5', C_9, D_25), '#skF_4') | ~m1_subset_1(D_25, k3_zfmisc_1(A_7, '#skF_5', C_9)) | k1_xboole_0=C_9 | k1_xboole_0='#skF_5' | k1_xboole_0=A_7)), inference(resolution, [status(thm)], [c_10, c_210])).
% 2.44/1.38  tff(c_230, plain, (![A_169, C_170, D_171]: ('#skF_3'(A_169, '#skF_5', C_170, D_171)='#skF_7' | D_171!='#skF_8' | ~m1_subset_1('#skF_3'(A_169, '#skF_5', C_170, D_171), '#skF_6') | ~m1_subset_1('#skF_1'(A_169, '#skF_5', C_170, D_171), '#skF_4') | ~m1_subset_1(D_171, k3_zfmisc_1(A_169, '#skF_5', C_170)) | k1_xboole_0=C_170 | k1_xboole_0=A_169)), inference(negUnitSimplification, [status(thm)], [c_24, c_24, c_214])).
% 2.44/1.38  tff(c_234, plain, (![A_7, D_25]: ('#skF_3'(A_7, '#skF_5', '#skF_6', D_25)='#skF_7' | D_25!='#skF_8' | ~m1_subset_1('#skF_1'(A_7, '#skF_5', '#skF_6', D_25), '#skF_4') | ~m1_subset_1(D_25, k3_zfmisc_1(A_7, '#skF_5', '#skF_6')) | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k1_xboole_0=A_7)), inference(resolution, [status(thm)], [c_8, c_230])).
% 2.44/1.38  tff(c_239, plain, (![A_172, D_173]: ('#skF_3'(A_172, '#skF_5', '#skF_6', D_173)='#skF_7' | D_173!='#skF_8' | ~m1_subset_1('#skF_1'(A_172, '#skF_5', '#skF_6', D_173), '#skF_4') | ~m1_subset_1(D_173, k3_zfmisc_1(A_172, '#skF_5', '#skF_6')) | k1_xboole_0=A_172)), inference(negUnitSimplification, [status(thm)], [c_24, c_22, c_22, c_234])).
% 2.44/1.38  tff(c_243, plain, (![D_25]: ('#skF_3'('#skF_4', '#skF_5', '#skF_6', D_25)='#skF_7' | D_25!='#skF_8' | ~m1_subset_1(D_25, k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6')) | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4')), inference(resolution, [status(thm)], [c_12, c_239])).
% 2.44/1.38  tff(c_248, plain, (![D_174]: ('#skF_3'('#skF_4', '#skF_5', '#skF_6', D_174)='#skF_7' | D_174!='#skF_8' | ~m1_subset_1(D_174, k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6')))), inference(negUnitSimplification, [status(thm)], [c_26, c_24, c_22, c_26, c_243])).
% 2.44/1.38  tff(c_267, plain, ('#skF_3'('#skF_4', '#skF_5', '#skF_6', '#skF_8')='#skF_7'), inference(resolution, [status(thm)], [c_30, c_248])).
% 2.44/1.38  tff(c_6, plain, (![A_7, B_8, C_9, D_25]: (k3_mcart_1('#skF_1'(A_7, B_8, C_9, D_25), '#skF_2'(A_7, B_8, C_9, D_25), '#skF_3'(A_7, B_8, C_9, D_25))=D_25 | ~m1_subset_1(D_25, k3_zfmisc_1(A_7, B_8, C_9)) | k1_xboole_0=C_9 | k1_xboole_0=B_8 | k1_xboole_0=A_7)), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.44/1.38  tff(c_274, plain, (k3_mcart_1('#skF_1'('#skF_4', '#skF_5', '#skF_6', '#skF_8'), '#skF_2'('#skF_4', '#skF_5', '#skF_6', '#skF_8'), '#skF_7')='#skF_8' | ~m1_subset_1('#skF_8', k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6')) | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_267, c_6])).
% 2.44/1.38  tff(c_285, plain, (k3_mcart_1('#skF_1'('#skF_4', '#skF_5', '#skF_6', '#skF_8'), '#skF_2'('#skF_4', '#skF_5', '#skF_6', '#skF_8'), '#skF_7')='#skF_8' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_30, c_274])).
% 2.44/1.38  tff(c_286, plain, (k3_mcart_1('#skF_1'('#skF_4', '#skF_5', '#skF_6', '#skF_8'), '#skF_2'('#skF_4', '#skF_5', '#skF_6', '#skF_8'), '#skF_7')='#skF_8'), inference(negUnitSimplification, [status(thm)], [c_26, c_24, c_22, c_285])).
% 2.44/1.38  tff(c_14, plain, (![C_39, B_38, G_53, F_52, E_51, A_37]: (k7_mcart_1(A_37, B_38, C_39, k3_mcart_1(E_51, F_52, G_53))=G_53 | ~m1_subset_1(k3_mcart_1(E_51, F_52, G_53), k3_zfmisc_1(A_37, B_38, C_39)) | k1_xboole_0=C_39 | k1_xboole_0=B_38 | k1_xboole_0=A_37)), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.44/1.38  tff(c_312, plain, (![A_37, B_38, C_39]: (k7_mcart_1(A_37, B_38, C_39, k3_mcart_1('#skF_1'('#skF_4', '#skF_5', '#skF_6', '#skF_8'), '#skF_2'('#skF_4', '#skF_5', '#skF_6', '#skF_8'), '#skF_7'))='#skF_7' | ~m1_subset_1('#skF_8', k3_zfmisc_1(A_37, B_38, C_39)) | k1_xboole_0=C_39 | k1_xboole_0=B_38 | k1_xboole_0=A_37)), inference(superposition, [status(thm), theory('equality')], [c_286, c_14])).
% 2.44/1.38  tff(c_339, plain, (![A_175, B_176, C_177]: (k7_mcart_1(A_175, B_176, C_177, '#skF_8')='#skF_7' | ~m1_subset_1('#skF_8', k3_zfmisc_1(A_175, B_176, C_177)) | k1_xboole_0=C_177 | k1_xboole_0=B_176 | k1_xboole_0=A_175)), inference(demodulation, [status(thm), theory('equality')], [c_286, c_312])).
% 2.44/1.38  tff(c_345, plain, (k7_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_8')='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_30, c_339])).
% 2.44/1.38  tff(c_349, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26, c_24, c_22, c_20, c_345])).
% 2.44/1.38  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.44/1.38  
% 2.44/1.38  Inference rules
% 2.44/1.38  ----------------------
% 2.44/1.38  #Ref     : 0
% 2.44/1.38  #Sup     : 74
% 2.44/1.38  #Fact    : 0
% 2.44/1.38  #Define  : 0
% 2.44/1.38  #Split   : 0
% 2.44/1.38  #Chain   : 0
% 2.44/1.38  #Close   : 0
% 2.44/1.38  
% 2.44/1.38  Ordering : KBO
% 2.44/1.38  
% 2.44/1.38  Simplification rules
% 2.44/1.38  ----------------------
% 2.44/1.38  #Subsume      : 7
% 2.44/1.38  #Demod        : 47
% 2.44/1.38  #Tautology    : 20
% 2.44/1.38  #SimpNegUnit  : 7
% 2.44/1.38  #BackRed      : 0
% 2.44/1.38  
% 2.44/1.38  #Partial instantiations: 0
% 2.44/1.38  #Strategies tried      : 1
% 2.44/1.38  
% 2.44/1.38  Timing (in seconds)
% 2.44/1.38  ----------------------
% 2.69/1.39  Preprocessing        : 0.32
% 2.69/1.39  Parsing              : 0.17
% 2.69/1.39  CNF conversion       : 0.03
% 2.69/1.39  Main loop            : 0.26
% 2.69/1.39  Inferencing          : 0.11
% 2.69/1.39  Reduction            : 0.08
% 2.69/1.39  Demodulation         : 0.06
% 2.69/1.39  BG Simplification    : 0.02
% 2.69/1.39  Subsumption          : 0.05
% 2.69/1.39  Abstraction          : 0.02
% 2.69/1.39  MUC search           : 0.00
% 2.69/1.39  Cooper               : 0.00
% 2.69/1.39  Total                : 0.61
% 2.69/1.39  Index Insertion      : 0.00
% 2.69/1.39  Index Deletion       : 0.00
% 2.69/1.39  Index Matching       : 0.00
% 2.69/1.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------
