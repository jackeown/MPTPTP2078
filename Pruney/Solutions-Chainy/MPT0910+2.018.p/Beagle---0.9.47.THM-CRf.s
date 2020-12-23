%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:01 EST 2020

% Result     : Theorem 2.56s
% Output     : CNFRefutation 2.56s
% Verified   : 
% Statistics : Number of formulae       :   51 ( 139 expanded)
%              Number of leaves         :   24 (  67 expanded)
%              Depth                    :   16
%              Number of atoms          :  137 ( 663 expanded)
%              Number of equality atoms :   95 ( 417 expanded)
%              Maximal formula depth    :   17 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_subset_1 > k7_mcart_1 > k6_mcart_1 > k5_mcart_1 > k3_zfmisc_1 > k3_mcart_1 > k4_tarski > #nlpp > k2_mcart_1 > k1_mcart_1 > k1_xboole_0 > #skF_7 > #skF_5 > #skF_2 > #skF_6 > #skF_8 > #skF_4 > #skF_3 > #skF_1

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

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k6_mcart_1,type,(
    k6_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_122,negated_conjecture,(
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

tff(f_56,axiom,(
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

tff(f_98,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k3_zfmisc_1(A,B,C))
     => ~ ( A != k1_xboole_0
          & B != k1_xboole_0
          & C != k1_xboole_0
          & ? [E,F,G] :
              ( D = k3_mcart_1(E,F,G)
              & ~ ( k5_mcart_1(A,B,C,D) = E
                  & k6_mcart_1(A,B,C,D) = F
                  & k7_mcart_1(A,B,C,D) = G ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t68_mcart_1)).

tff(c_32,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_30,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_28,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_26,plain,(
    k6_mcart_1('#skF_4','#skF_5','#skF_6','#skF_8') != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_36,plain,(
    m1_subset_1('#skF_8',k3_zfmisc_1('#skF_4','#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_12,plain,(
    ! [A_8,B_9,C_10,D_26] :
      ( m1_subset_1('#skF_1'(A_8,B_9,C_10,D_26),A_8)
      | ~ m1_subset_1(D_26,k3_zfmisc_1(A_8,B_9,C_10))
      | k1_xboole_0 = C_10
      | k1_xboole_0 = B_9
      | k1_xboole_0 = A_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_8,plain,(
    ! [A_8,B_9,C_10,D_26] :
      ( m1_subset_1('#skF_3'(A_8,B_9,C_10,D_26),C_10)
      | ~ m1_subset_1(D_26,k3_zfmisc_1(A_8,B_9,C_10))
      | k1_xboole_0 = C_10
      | k1_xboole_0 = B_9
      | k1_xboole_0 = A_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_10,plain,(
    ! [A_8,B_9,C_10,D_26] :
      ( m1_subset_1('#skF_2'(A_8,B_9,C_10,D_26),B_9)
      | ~ m1_subset_1(D_26,k3_zfmisc_1(A_8,B_9,C_10))
      | k1_xboole_0 = C_10
      | k1_xboole_0 = B_9
      | k1_xboole_0 = A_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_201,plain,(
    ! [A_134,B_135,C_136,D_137] :
      ( k3_mcart_1('#skF_1'(A_134,B_135,C_136,D_137),'#skF_2'(A_134,B_135,C_136,D_137),'#skF_3'(A_134,B_135,C_136,D_137)) = D_137
      | ~ m1_subset_1(D_137,k3_zfmisc_1(A_134,B_135,C_136))
      | k1_xboole_0 = C_136
      | k1_xboole_0 = B_135
      | k1_xboole_0 = A_134 ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_34,plain,(
    ! [G_64,F_60,H_66] :
      ( G_64 = '#skF_7'
      | k3_mcart_1(F_60,G_64,H_66) != '#skF_8'
      | ~ m1_subset_1(H_66,'#skF_6')
      | ~ m1_subset_1(G_64,'#skF_5')
      | ~ m1_subset_1(F_60,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_260,plain,(
    ! [A_158,B_159,C_160,D_161] :
      ( '#skF_2'(A_158,B_159,C_160,D_161) = '#skF_7'
      | D_161 != '#skF_8'
      | ~ m1_subset_1('#skF_3'(A_158,B_159,C_160,D_161),'#skF_6')
      | ~ m1_subset_1('#skF_2'(A_158,B_159,C_160,D_161),'#skF_5')
      | ~ m1_subset_1('#skF_1'(A_158,B_159,C_160,D_161),'#skF_4')
      | ~ m1_subset_1(D_161,k3_zfmisc_1(A_158,B_159,C_160))
      | k1_xboole_0 = C_160
      | k1_xboole_0 = B_159
      | k1_xboole_0 = A_158 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_201,c_34])).

tff(c_264,plain,(
    ! [A_8,C_10,D_26] :
      ( '#skF_2'(A_8,'#skF_5',C_10,D_26) = '#skF_7'
      | D_26 != '#skF_8'
      | ~ m1_subset_1('#skF_3'(A_8,'#skF_5',C_10,D_26),'#skF_6')
      | ~ m1_subset_1('#skF_1'(A_8,'#skF_5',C_10,D_26),'#skF_4')
      | ~ m1_subset_1(D_26,k3_zfmisc_1(A_8,'#skF_5',C_10))
      | k1_xboole_0 = C_10
      | k1_xboole_0 = '#skF_5'
      | k1_xboole_0 = A_8 ) ),
    inference(resolution,[status(thm)],[c_10,c_260])).

tff(c_269,plain,(
    ! [A_162,C_163,D_164] :
      ( '#skF_2'(A_162,'#skF_5',C_163,D_164) = '#skF_7'
      | D_164 != '#skF_8'
      | ~ m1_subset_1('#skF_3'(A_162,'#skF_5',C_163,D_164),'#skF_6')
      | ~ m1_subset_1('#skF_1'(A_162,'#skF_5',C_163,D_164),'#skF_4')
      | ~ m1_subset_1(D_164,k3_zfmisc_1(A_162,'#skF_5',C_163))
      | k1_xboole_0 = C_163
      | k1_xboole_0 = A_162 ) ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_30,c_264])).

tff(c_273,plain,(
    ! [A_8,D_26] :
      ( '#skF_2'(A_8,'#skF_5','#skF_6',D_26) = '#skF_7'
      | D_26 != '#skF_8'
      | ~ m1_subset_1('#skF_1'(A_8,'#skF_5','#skF_6',D_26),'#skF_4')
      | ~ m1_subset_1(D_26,k3_zfmisc_1(A_8,'#skF_5','#skF_6'))
      | k1_xboole_0 = '#skF_6'
      | k1_xboole_0 = '#skF_5'
      | k1_xboole_0 = A_8 ) ),
    inference(resolution,[status(thm)],[c_8,c_269])).

tff(c_278,plain,(
    ! [A_165,D_166] :
      ( '#skF_2'(A_165,'#skF_5','#skF_6',D_166) = '#skF_7'
      | D_166 != '#skF_8'
      | ~ m1_subset_1('#skF_1'(A_165,'#skF_5','#skF_6',D_166),'#skF_4')
      | ~ m1_subset_1(D_166,k3_zfmisc_1(A_165,'#skF_5','#skF_6'))
      | k1_xboole_0 = A_165 ) ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_28,c_28,c_273])).

tff(c_282,plain,(
    ! [D_26] :
      ( '#skF_2'('#skF_4','#skF_5','#skF_6',D_26) = '#skF_7'
      | D_26 != '#skF_8'
      | ~ m1_subset_1(D_26,k3_zfmisc_1('#skF_4','#skF_5','#skF_6'))
      | k1_xboole_0 = '#skF_6'
      | k1_xboole_0 = '#skF_5'
      | k1_xboole_0 = '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_12,c_278])).

tff(c_287,plain,(
    ! [D_167] :
      ( '#skF_2'('#skF_4','#skF_5','#skF_6',D_167) = '#skF_7'
      | D_167 != '#skF_8'
      | ~ m1_subset_1(D_167,k3_zfmisc_1('#skF_4','#skF_5','#skF_6')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_30,c_28,c_32,c_282])).

tff(c_311,plain,(
    '#skF_2'('#skF_4','#skF_5','#skF_6','#skF_8') = '#skF_7' ),
    inference(resolution,[status(thm)],[c_36,c_287])).

tff(c_6,plain,(
    ! [A_8,B_9,C_10,D_26] :
      ( k3_mcart_1('#skF_1'(A_8,B_9,C_10,D_26),'#skF_2'(A_8,B_9,C_10,D_26),'#skF_3'(A_8,B_9,C_10,D_26)) = D_26
      | ~ m1_subset_1(D_26,k3_zfmisc_1(A_8,B_9,C_10))
      | k1_xboole_0 = C_10
      | k1_xboole_0 = B_9
      | k1_xboole_0 = A_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_318,plain,
    ( k3_mcart_1('#skF_1'('#skF_4','#skF_5','#skF_6','#skF_8'),'#skF_7','#skF_3'('#skF_4','#skF_5','#skF_6','#skF_8')) = '#skF_8'
    | ~ m1_subset_1('#skF_8',k3_zfmisc_1('#skF_4','#skF_5','#skF_6'))
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_311,c_6])).

tff(c_329,plain,
    ( k3_mcart_1('#skF_1'('#skF_4','#skF_5','#skF_6','#skF_8'),'#skF_7','#skF_3'('#skF_4','#skF_5','#skF_6','#skF_8')) = '#skF_8'
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_318])).

tff(c_330,plain,(
    k3_mcart_1('#skF_1'('#skF_4','#skF_5','#skF_6','#skF_8'),'#skF_7','#skF_3'('#skF_4','#skF_5','#skF_6','#skF_8')) = '#skF_8' ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_30,c_28,c_329])).

tff(c_22,plain,(
    ! [E_50,C_45,A_43,B_44,G_52,F_51] :
      ( k6_mcart_1(A_43,B_44,C_45,k3_mcart_1(E_50,F_51,G_52)) = F_51
      | k1_xboole_0 = C_45
      | k1_xboole_0 = B_44
      | k1_xboole_0 = A_43
      | ~ m1_subset_1(k3_mcart_1(E_50,F_51,G_52),k3_zfmisc_1(A_43,B_44,C_45)) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_370,plain,(
    ! [A_43,B_44,C_45] :
      ( k6_mcart_1(A_43,B_44,C_45,k3_mcart_1('#skF_1'('#skF_4','#skF_5','#skF_6','#skF_8'),'#skF_7','#skF_3'('#skF_4','#skF_5','#skF_6','#skF_8'))) = '#skF_7'
      | k1_xboole_0 = C_45
      | k1_xboole_0 = B_44
      | k1_xboole_0 = A_43
      | ~ m1_subset_1('#skF_8',k3_zfmisc_1(A_43,B_44,C_45)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_330,c_22])).

tff(c_388,plain,(
    ! [A_174,B_175,C_176] :
      ( k6_mcart_1(A_174,B_175,C_176,'#skF_8') = '#skF_7'
      | k1_xboole_0 = C_176
      | k1_xboole_0 = B_175
      | k1_xboole_0 = A_174
      | ~ m1_subset_1('#skF_8',k3_zfmisc_1(A_174,B_175,C_176)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_330,c_370])).

tff(c_391,plain,
    ( k6_mcart_1('#skF_4','#skF_5','#skF_6','#skF_8') = '#skF_7'
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_36,c_388])).

tff(c_395,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_30,c_28,c_26,c_391])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:45:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.56/1.36  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.56/1.36  
% 2.56/1.36  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.56/1.37  %$ m1_subset_1 > k7_mcart_1 > k6_mcart_1 > k5_mcart_1 > k3_zfmisc_1 > k3_mcart_1 > k4_tarski > #nlpp > k2_mcart_1 > k1_mcart_1 > k1_xboole_0 > #skF_7 > #skF_5 > #skF_2 > #skF_6 > #skF_8 > #skF_4 > #skF_3 > #skF_1
% 2.56/1.37  
% 2.56/1.37  %Foreground sorts:
% 2.56/1.37  
% 2.56/1.37  
% 2.56/1.37  %Background operators:
% 2.56/1.37  
% 2.56/1.37  
% 2.56/1.37  %Foreground operators:
% 2.56/1.37  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.56/1.37  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.56/1.37  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.56/1.37  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 2.56/1.37  tff('#skF_7', type, '#skF_7': $i).
% 2.56/1.37  tff('#skF_5', type, '#skF_5': $i).
% 2.56/1.37  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 2.56/1.37  tff('#skF_6', type, '#skF_6': $i).
% 2.56/1.37  tff(k7_mcart_1, type, k7_mcart_1: ($i * $i * $i * $i) > $i).
% 2.56/1.37  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 2.56/1.37  tff('#skF_8', type, '#skF_8': $i).
% 2.56/1.37  tff(k5_mcart_1, type, k5_mcart_1: ($i * $i * $i * $i) > $i).
% 2.56/1.37  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.56/1.37  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 2.56/1.37  tff('#skF_4', type, '#skF_4': $i).
% 2.56/1.37  tff(k6_mcart_1, type, k6_mcart_1: ($i * $i * $i * $i) > $i).
% 2.56/1.37  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.56/1.37  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 2.56/1.37  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 2.56/1.37  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 2.56/1.37  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.56/1.37  
% 2.56/1.38  tff(f_122, negated_conjecture, ~(![A, B, C, D, E]: (m1_subset_1(E, k3_zfmisc_1(A, B, C)) => ((![F]: (m1_subset_1(F, A) => (![G]: (m1_subset_1(G, B) => (![H]: (m1_subset_1(H, C) => ((E = k3_mcart_1(F, G, H)) => (D = G)))))))) => ((((A = k1_xboole_0) | (B = k1_xboole_0)) | (C = k1_xboole_0)) | (D = k6_mcart_1(A, B, C, E)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_mcart_1)).
% 2.56/1.38  tff(f_56, axiom, (![A, B, C]: ~(((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & (?[D]: (m1_subset_1(D, k3_zfmisc_1(A, B, C)) & (![E]: (m1_subset_1(E, A) => (![F]: (m1_subset_1(F, B) => (![G]: (m1_subset_1(G, C) => ~(D = k3_mcart_1(E, F, G)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l44_mcart_1)).
% 2.56/1.38  tff(f_98, axiom, (![A, B, C, D]: (m1_subset_1(D, k3_zfmisc_1(A, B, C)) => ~(((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & (?[E, F, G]: ((D = k3_mcart_1(E, F, G)) & ~(((k5_mcart_1(A, B, C, D) = E) & (k6_mcart_1(A, B, C, D) = F)) & (k7_mcart_1(A, B, C, D) = G))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t68_mcart_1)).
% 2.56/1.38  tff(c_32, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_122])).
% 2.56/1.38  tff(c_30, plain, (k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_122])).
% 2.56/1.38  tff(c_28, plain, (k1_xboole_0!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_122])).
% 2.56/1.38  tff(c_26, plain, (k6_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_8')!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_122])).
% 2.56/1.38  tff(c_36, plain, (m1_subset_1('#skF_8', k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_122])).
% 2.56/1.38  tff(c_12, plain, (![A_8, B_9, C_10, D_26]: (m1_subset_1('#skF_1'(A_8, B_9, C_10, D_26), A_8) | ~m1_subset_1(D_26, k3_zfmisc_1(A_8, B_9, C_10)) | k1_xboole_0=C_10 | k1_xboole_0=B_9 | k1_xboole_0=A_8)), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.56/1.38  tff(c_8, plain, (![A_8, B_9, C_10, D_26]: (m1_subset_1('#skF_3'(A_8, B_9, C_10, D_26), C_10) | ~m1_subset_1(D_26, k3_zfmisc_1(A_8, B_9, C_10)) | k1_xboole_0=C_10 | k1_xboole_0=B_9 | k1_xboole_0=A_8)), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.56/1.38  tff(c_10, plain, (![A_8, B_9, C_10, D_26]: (m1_subset_1('#skF_2'(A_8, B_9, C_10, D_26), B_9) | ~m1_subset_1(D_26, k3_zfmisc_1(A_8, B_9, C_10)) | k1_xboole_0=C_10 | k1_xboole_0=B_9 | k1_xboole_0=A_8)), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.56/1.38  tff(c_201, plain, (![A_134, B_135, C_136, D_137]: (k3_mcart_1('#skF_1'(A_134, B_135, C_136, D_137), '#skF_2'(A_134, B_135, C_136, D_137), '#skF_3'(A_134, B_135, C_136, D_137))=D_137 | ~m1_subset_1(D_137, k3_zfmisc_1(A_134, B_135, C_136)) | k1_xboole_0=C_136 | k1_xboole_0=B_135 | k1_xboole_0=A_134)), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.56/1.38  tff(c_34, plain, (![G_64, F_60, H_66]: (G_64='#skF_7' | k3_mcart_1(F_60, G_64, H_66)!='#skF_8' | ~m1_subset_1(H_66, '#skF_6') | ~m1_subset_1(G_64, '#skF_5') | ~m1_subset_1(F_60, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_122])).
% 2.56/1.38  tff(c_260, plain, (![A_158, B_159, C_160, D_161]: ('#skF_2'(A_158, B_159, C_160, D_161)='#skF_7' | D_161!='#skF_8' | ~m1_subset_1('#skF_3'(A_158, B_159, C_160, D_161), '#skF_6') | ~m1_subset_1('#skF_2'(A_158, B_159, C_160, D_161), '#skF_5') | ~m1_subset_1('#skF_1'(A_158, B_159, C_160, D_161), '#skF_4') | ~m1_subset_1(D_161, k3_zfmisc_1(A_158, B_159, C_160)) | k1_xboole_0=C_160 | k1_xboole_0=B_159 | k1_xboole_0=A_158)), inference(superposition, [status(thm), theory('equality')], [c_201, c_34])).
% 2.56/1.38  tff(c_264, plain, (![A_8, C_10, D_26]: ('#skF_2'(A_8, '#skF_5', C_10, D_26)='#skF_7' | D_26!='#skF_8' | ~m1_subset_1('#skF_3'(A_8, '#skF_5', C_10, D_26), '#skF_6') | ~m1_subset_1('#skF_1'(A_8, '#skF_5', C_10, D_26), '#skF_4') | ~m1_subset_1(D_26, k3_zfmisc_1(A_8, '#skF_5', C_10)) | k1_xboole_0=C_10 | k1_xboole_0='#skF_5' | k1_xboole_0=A_8)), inference(resolution, [status(thm)], [c_10, c_260])).
% 2.56/1.38  tff(c_269, plain, (![A_162, C_163, D_164]: ('#skF_2'(A_162, '#skF_5', C_163, D_164)='#skF_7' | D_164!='#skF_8' | ~m1_subset_1('#skF_3'(A_162, '#skF_5', C_163, D_164), '#skF_6') | ~m1_subset_1('#skF_1'(A_162, '#skF_5', C_163, D_164), '#skF_4') | ~m1_subset_1(D_164, k3_zfmisc_1(A_162, '#skF_5', C_163)) | k1_xboole_0=C_163 | k1_xboole_0=A_162)), inference(negUnitSimplification, [status(thm)], [c_30, c_30, c_264])).
% 2.56/1.38  tff(c_273, plain, (![A_8, D_26]: ('#skF_2'(A_8, '#skF_5', '#skF_6', D_26)='#skF_7' | D_26!='#skF_8' | ~m1_subset_1('#skF_1'(A_8, '#skF_5', '#skF_6', D_26), '#skF_4') | ~m1_subset_1(D_26, k3_zfmisc_1(A_8, '#skF_5', '#skF_6')) | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k1_xboole_0=A_8)), inference(resolution, [status(thm)], [c_8, c_269])).
% 2.56/1.38  tff(c_278, plain, (![A_165, D_166]: ('#skF_2'(A_165, '#skF_5', '#skF_6', D_166)='#skF_7' | D_166!='#skF_8' | ~m1_subset_1('#skF_1'(A_165, '#skF_5', '#skF_6', D_166), '#skF_4') | ~m1_subset_1(D_166, k3_zfmisc_1(A_165, '#skF_5', '#skF_6')) | k1_xboole_0=A_165)), inference(negUnitSimplification, [status(thm)], [c_30, c_28, c_28, c_273])).
% 2.56/1.38  tff(c_282, plain, (![D_26]: ('#skF_2'('#skF_4', '#skF_5', '#skF_6', D_26)='#skF_7' | D_26!='#skF_8' | ~m1_subset_1(D_26, k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6')) | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4')), inference(resolution, [status(thm)], [c_12, c_278])).
% 2.56/1.38  tff(c_287, plain, (![D_167]: ('#skF_2'('#skF_4', '#skF_5', '#skF_6', D_167)='#skF_7' | D_167!='#skF_8' | ~m1_subset_1(D_167, k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6')))), inference(negUnitSimplification, [status(thm)], [c_32, c_30, c_28, c_32, c_282])).
% 2.56/1.38  tff(c_311, plain, ('#skF_2'('#skF_4', '#skF_5', '#skF_6', '#skF_8')='#skF_7'), inference(resolution, [status(thm)], [c_36, c_287])).
% 2.56/1.38  tff(c_6, plain, (![A_8, B_9, C_10, D_26]: (k3_mcart_1('#skF_1'(A_8, B_9, C_10, D_26), '#skF_2'(A_8, B_9, C_10, D_26), '#skF_3'(A_8, B_9, C_10, D_26))=D_26 | ~m1_subset_1(D_26, k3_zfmisc_1(A_8, B_9, C_10)) | k1_xboole_0=C_10 | k1_xboole_0=B_9 | k1_xboole_0=A_8)), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.56/1.38  tff(c_318, plain, (k3_mcart_1('#skF_1'('#skF_4', '#skF_5', '#skF_6', '#skF_8'), '#skF_7', '#skF_3'('#skF_4', '#skF_5', '#skF_6', '#skF_8'))='#skF_8' | ~m1_subset_1('#skF_8', k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6')) | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_311, c_6])).
% 2.56/1.38  tff(c_329, plain, (k3_mcart_1('#skF_1'('#skF_4', '#skF_5', '#skF_6', '#skF_8'), '#skF_7', '#skF_3'('#skF_4', '#skF_5', '#skF_6', '#skF_8'))='#skF_8' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_318])).
% 2.56/1.38  tff(c_330, plain, (k3_mcart_1('#skF_1'('#skF_4', '#skF_5', '#skF_6', '#skF_8'), '#skF_7', '#skF_3'('#skF_4', '#skF_5', '#skF_6', '#skF_8'))='#skF_8'), inference(negUnitSimplification, [status(thm)], [c_32, c_30, c_28, c_329])).
% 2.56/1.38  tff(c_22, plain, (![E_50, C_45, A_43, B_44, G_52, F_51]: (k6_mcart_1(A_43, B_44, C_45, k3_mcart_1(E_50, F_51, G_52))=F_51 | k1_xboole_0=C_45 | k1_xboole_0=B_44 | k1_xboole_0=A_43 | ~m1_subset_1(k3_mcart_1(E_50, F_51, G_52), k3_zfmisc_1(A_43, B_44, C_45)))), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.56/1.38  tff(c_370, plain, (![A_43, B_44, C_45]: (k6_mcart_1(A_43, B_44, C_45, k3_mcart_1('#skF_1'('#skF_4', '#skF_5', '#skF_6', '#skF_8'), '#skF_7', '#skF_3'('#skF_4', '#skF_5', '#skF_6', '#skF_8')))='#skF_7' | k1_xboole_0=C_45 | k1_xboole_0=B_44 | k1_xboole_0=A_43 | ~m1_subset_1('#skF_8', k3_zfmisc_1(A_43, B_44, C_45)))), inference(superposition, [status(thm), theory('equality')], [c_330, c_22])).
% 2.56/1.38  tff(c_388, plain, (![A_174, B_175, C_176]: (k6_mcart_1(A_174, B_175, C_176, '#skF_8')='#skF_7' | k1_xboole_0=C_176 | k1_xboole_0=B_175 | k1_xboole_0=A_174 | ~m1_subset_1('#skF_8', k3_zfmisc_1(A_174, B_175, C_176)))), inference(demodulation, [status(thm), theory('equality')], [c_330, c_370])).
% 2.56/1.38  tff(c_391, plain, (k6_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_8')='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_36, c_388])).
% 2.56/1.38  tff(c_395, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_30, c_28, c_26, c_391])).
% 2.56/1.38  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.56/1.38  
% 2.56/1.38  Inference rules
% 2.56/1.38  ----------------------
% 2.56/1.38  #Ref     : 0
% 2.56/1.38  #Sup     : 79
% 2.56/1.38  #Fact    : 0
% 2.56/1.38  #Define  : 0
% 2.56/1.38  #Split   : 0
% 2.56/1.38  #Chain   : 0
% 2.56/1.38  #Close   : 0
% 2.56/1.38  
% 2.56/1.38  Ordering : KBO
% 2.56/1.38  
% 2.56/1.38  Simplification rules
% 2.56/1.38  ----------------------
% 2.56/1.38  #Subsume      : 4
% 2.56/1.38  #Demod        : 30
% 2.56/1.38  #Tautology    : 24
% 2.56/1.38  #SimpNegUnit  : 10
% 2.56/1.38  #BackRed      : 0
% 2.56/1.38  
% 2.56/1.38  #Partial instantiations: 0
% 2.56/1.38  #Strategies tried      : 1
% 2.56/1.38  
% 2.56/1.38  Timing (in seconds)
% 2.56/1.38  ----------------------
% 2.56/1.38  Preprocessing        : 0.32
% 2.56/1.38  Parsing              : 0.16
% 2.56/1.38  CNF conversion       : 0.03
% 2.56/1.38  Main loop            : 0.29
% 2.56/1.38  Inferencing          : 0.12
% 2.56/1.38  Reduction            : 0.08
% 2.56/1.38  Demodulation         : 0.06
% 2.56/1.38  BG Simplification    : 0.03
% 2.56/1.38  Subsumption          : 0.05
% 2.56/1.38  Abstraction          : 0.03
% 2.56/1.38  MUC search           : 0.00
% 2.56/1.38  Cooper               : 0.00
% 2.56/1.38  Total                : 0.64
% 2.56/1.38  Index Insertion      : 0.00
% 2.56/1.38  Index Deletion       : 0.00
% 2.56/1.38  Index Matching       : 0.00
% 2.56/1.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------
