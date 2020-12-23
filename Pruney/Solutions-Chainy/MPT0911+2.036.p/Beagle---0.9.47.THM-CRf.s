%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:06 EST 2020

% Result     : Theorem 3.45s
% Output     : CNFRefutation 3.51s
% Verified   : 
% Statistics : Number of formulae       :   52 (  89 expanded)
%              Number of leaves         :   24 (  47 expanded)
%              Depth                    :   15
%              Number of atoms          :  142 ( 378 expanded)
%              Number of equality atoms :  100 ( 242 expanded)
%              Maximal formula depth    :   17 (   6 average)
%              Maximal term depth       :    3 (   1 average)

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

tff(f_78,axiom,(
    ! [A,B,C] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & C != k1_xboole_0
        & ~ ! [D] :
              ( m1_subset_1(D,k3_zfmisc_1(A,B,C))
             => D = k3_mcart_1(k5_mcart_1(A,B,C,D),k6_mcart_1(A,B,C,D),k7_mcart_1(A,B,C,D)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_mcart_1)).

tff(f_62,axiom,(
    ! [A,B,C,D,E,F] :
      ( k3_mcart_1(A,B,C) = k3_mcart_1(D,E,F)
     => ( A = D
        & B = E
        & C = F ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_mcart_1)).

tff(c_28,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_26,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_24,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_22,plain,(
    k7_mcart_1('#skF_4','#skF_5','#skF_6','#skF_8') != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_32,plain,(
    m1_subset_1('#skF_8',k3_zfmisc_1('#skF_4','#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

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

tff(c_200,plain,(
    ! [A_158,B_159,C_160,D_161] :
      ( k3_mcart_1('#skF_1'(A_158,B_159,C_160,D_161),'#skF_2'(A_158,B_159,C_160,D_161),'#skF_3'(A_158,B_159,C_160,D_161)) = D_161
      | ~ m1_subset_1(D_161,k3_zfmisc_1(A_158,B_159,C_160))
      | k1_xboole_0 = C_160
      | k1_xboole_0 = B_159
      | k1_xboole_0 = A_158 ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_30,plain,(
    ! [H_61,F_55,G_59] :
      ( H_61 = '#skF_7'
      | k3_mcart_1(F_55,G_59,H_61) != '#skF_8'
      | ~ m1_subset_1(H_61,'#skF_6')
      | ~ m1_subset_1(G_59,'#skF_5')
      | ~ m1_subset_1(F_55,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_265,plain,(
    ! [A_162,B_163,C_164,D_165] :
      ( '#skF_3'(A_162,B_163,C_164,D_165) = '#skF_7'
      | D_165 != '#skF_8'
      | ~ m1_subset_1('#skF_3'(A_162,B_163,C_164,D_165),'#skF_6')
      | ~ m1_subset_1('#skF_2'(A_162,B_163,C_164,D_165),'#skF_5')
      | ~ m1_subset_1('#skF_1'(A_162,B_163,C_164,D_165),'#skF_4')
      | ~ m1_subset_1(D_165,k3_zfmisc_1(A_162,B_163,C_164))
      | k1_xboole_0 = C_164
      | k1_xboole_0 = B_163
      | k1_xboole_0 = A_162 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_200,c_30])).

tff(c_269,plain,(
    ! [A_7,C_9,D_25] :
      ( '#skF_3'(A_7,'#skF_5',C_9,D_25) = '#skF_7'
      | D_25 != '#skF_8'
      | ~ m1_subset_1('#skF_3'(A_7,'#skF_5',C_9,D_25),'#skF_6')
      | ~ m1_subset_1('#skF_1'(A_7,'#skF_5',C_9,D_25),'#skF_4')
      | ~ m1_subset_1(D_25,k3_zfmisc_1(A_7,'#skF_5',C_9))
      | k1_xboole_0 = C_9
      | k1_xboole_0 = '#skF_5'
      | k1_xboole_0 = A_7 ) ),
    inference(resolution,[status(thm)],[c_10,c_265])).

tff(c_405,plain,(
    ! [A_206,C_207,D_208] :
      ( '#skF_3'(A_206,'#skF_5',C_207,D_208) = '#skF_7'
      | D_208 != '#skF_8'
      | ~ m1_subset_1('#skF_3'(A_206,'#skF_5',C_207,D_208),'#skF_6')
      | ~ m1_subset_1('#skF_1'(A_206,'#skF_5',C_207,D_208),'#skF_4')
      | ~ m1_subset_1(D_208,k3_zfmisc_1(A_206,'#skF_5',C_207))
      | k1_xboole_0 = C_207
      | k1_xboole_0 = A_206 ) ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_26,c_269])).

tff(c_409,plain,(
    ! [A_7,D_25] :
      ( '#skF_3'(A_7,'#skF_5','#skF_6',D_25) = '#skF_7'
      | D_25 != '#skF_8'
      | ~ m1_subset_1('#skF_1'(A_7,'#skF_5','#skF_6',D_25),'#skF_4')
      | ~ m1_subset_1(D_25,k3_zfmisc_1(A_7,'#skF_5','#skF_6'))
      | k1_xboole_0 = '#skF_6'
      | k1_xboole_0 = '#skF_5'
      | k1_xboole_0 = A_7 ) ),
    inference(resolution,[status(thm)],[c_8,c_405])).

tff(c_442,plain,(
    ! [A_227,D_228] :
      ( '#skF_3'(A_227,'#skF_5','#skF_6',D_228) = '#skF_7'
      | D_228 != '#skF_8'
      | ~ m1_subset_1('#skF_1'(A_227,'#skF_5','#skF_6',D_228),'#skF_4')
      | ~ m1_subset_1(D_228,k3_zfmisc_1(A_227,'#skF_5','#skF_6'))
      | k1_xboole_0 = A_227 ) ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_24,c_24,c_409])).

tff(c_446,plain,(
    ! [D_25] :
      ( '#skF_3'('#skF_4','#skF_5','#skF_6',D_25) = '#skF_7'
      | D_25 != '#skF_8'
      | ~ m1_subset_1(D_25,k3_zfmisc_1('#skF_4','#skF_5','#skF_6'))
      | k1_xboole_0 = '#skF_6'
      | k1_xboole_0 = '#skF_5'
      | k1_xboole_0 = '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_12,c_442])).

tff(c_451,plain,(
    ! [D_229] :
      ( '#skF_3'('#skF_4','#skF_5','#skF_6',D_229) = '#skF_7'
      | D_229 != '#skF_8'
      | ~ m1_subset_1(D_229,k3_zfmisc_1('#skF_4','#skF_5','#skF_6')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_26,c_24,c_28,c_446])).

tff(c_470,plain,(
    '#skF_3'('#skF_4','#skF_5','#skF_6','#skF_8') = '#skF_7' ),
    inference(resolution,[status(thm)],[c_32,c_451])).

tff(c_6,plain,(
    ! [A_7,B_8,C_9,D_25] :
      ( k3_mcart_1('#skF_1'(A_7,B_8,C_9,D_25),'#skF_2'(A_7,B_8,C_9,D_25),'#skF_3'(A_7,B_8,C_9,D_25)) = D_25
      | ~ m1_subset_1(D_25,k3_zfmisc_1(A_7,B_8,C_9))
      | k1_xboole_0 = C_9
      | k1_xboole_0 = B_8
      | k1_xboole_0 = A_7 ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_477,plain,
    ( k3_mcart_1('#skF_1'('#skF_4','#skF_5','#skF_6','#skF_8'),'#skF_2'('#skF_4','#skF_5','#skF_6','#skF_8'),'#skF_7') = '#skF_8'
    | ~ m1_subset_1('#skF_8',k3_zfmisc_1('#skF_4','#skF_5','#skF_6'))
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_470,c_6])).

tff(c_488,plain,
    ( k3_mcart_1('#skF_1'('#skF_4','#skF_5','#skF_6','#skF_8'),'#skF_2'('#skF_4','#skF_5','#skF_6','#skF_8'),'#skF_7') = '#skF_8'
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_477])).

tff(c_489,plain,(
    k3_mcart_1('#skF_1'('#skF_4','#skF_5','#skF_6','#skF_8'),'#skF_2'('#skF_4','#skF_5','#skF_6','#skF_8'),'#skF_7') = '#skF_8' ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_26,c_24,c_488])).

tff(c_306,plain,(
    ! [A_188,B_189,C_190,D_191] :
      ( k3_mcart_1(k5_mcart_1(A_188,B_189,C_190,D_191),k6_mcart_1(A_188,B_189,C_190,D_191),k7_mcart_1(A_188,B_189,C_190,D_191)) = D_191
      | ~ m1_subset_1(D_191,k3_zfmisc_1(A_188,B_189,C_190))
      | k1_xboole_0 = C_190
      | k1_xboole_0 = B_189
      | k1_xboole_0 = A_188 ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_14,plain,(
    ! [C_39,B_38,A_37,D_40,F_42,E_41] :
      ( F_42 = C_39
      | k3_mcart_1(D_40,E_41,F_42) != k3_mcart_1(A_37,B_38,C_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_370,plain,(
    ! [C_190,B_189,D_40,F_42,A_188,E_41,D_191] :
      ( k7_mcart_1(A_188,B_189,C_190,D_191) = F_42
      | k3_mcart_1(D_40,E_41,F_42) != D_191
      | ~ m1_subset_1(D_191,k3_zfmisc_1(A_188,B_189,C_190))
      | k1_xboole_0 = C_190
      | k1_xboole_0 = B_189
      | k1_xboole_0 = A_188 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_306,c_14])).

tff(c_790,plain,(
    ! [A_303,B_304,C_305,D_306] :
      ( k7_mcart_1(A_303,B_304,C_305,D_306) = '#skF_7'
      | D_306 != '#skF_8'
      | ~ m1_subset_1(D_306,k3_zfmisc_1(A_303,B_304,C_305))
      | k1_xboole_0 = C_305
      | k1_xboole_0 = B_304
      | k1_xboole_0 = A_303 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_489,c_370])).

tff(c_808,plain,
    ( k7_mcart_1('#skF_4','#skF_5','#skF_6','#skF_8') = '#skF_7'
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_32,c_790])).

tff(c_815,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_26,c_24,c_22,c_808])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:29:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.45/1.55  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.51/1.55  
% 3.51/1.55  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.51/1.56  %$ m1_subset_1 > k7_mcart_1 > k6_mcart_1 > k5_mcart_1 > k3_zfmisc_1 > k3_mcart_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_7 > #skF_5 > #skF_2 > #skF_6 > #skF_8 > #skF_4 > #skF_3 > #skF_1
% 3.51/1.56  
% 3.51/1.56  %Foreground sorts:
% 3.51/1.56  
% 3.51/1.56  
% 3.51/1.56  %Background operators:
% 3.51/1.56  
% 3.51/1.56  
% 3.51/1.56  %Foreground operators:
% 3.51/1.56  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.51/1.56  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.51/1.56  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.51/1.56  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 3.51/1.56  tff('#skF_7', type, '#skF_7': $i).
% 3.51/1.56  tff('#skF_5', type, '#skF_5': $i).
% 3.51/1.56  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 3.51/1.56  tff('#skF_6', type, '#skF_6': $i).
% 3.51/1.56  tff(k7_mcart_1, type, k7_mcart_1: ($i * $i * $i * $i) > $i).
% 3.51/1.56  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 3.51/1.56  tff('#skF_8', type, '#skF_8': $i).
% 3.51/1.56  tff(k5_mcart_1, type, k5_mcart_1: ($i * $i * $i * $i) > $i).
% 3.51/1.56  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.51/1.56  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.51/1.56  tff('#skF_4', type, '#skF_4': $i).
% 3.51/1.56  tff(k6_mcart_1, type, k6_mcart_1: ($i * $i * $i * $i) > $i).
% 3.51/1.56  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.51/1.56  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 3.51/1.56  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 3.51/1.56  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.51/1.56  
% 3.51/1.57  tff(f_102, negated_conjecture, ~(![A, B, C, D, E]: (m1_subset_1(E, k3_zfmisc_1(A, B, C)) => ((![F]: (m1_subset_1(F, A) => (![G]: (m1_subset_1(G, B) => (![H]: (m1_subset_1(H, C) => ((E = k3_mcart_1(F, G, H)) => (D = H)))))))) => ((((A = k1_xboole_0) | (B = k1_xboole_0)) | (C = k1_xboole_0)) | (D = k7_mcart_1(A, B, C, E)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_mcart_1)).
% 3.51/1.57  tff(f_54, axiom, (![A, B, C]: ~(((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & (?[D]: (m1_subset_1(D, k3_zfmisc_1(A, B, C)) & (![E]: (m1_subset_1(E, A) => (![F]: (m1_subset_1(F, B) => (![G]: (m1_subset_1(G, C) => ~(D = k3_mcart_1(E, F, G)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l44_mcart_1)).
% 3.51/1.57  tff(f_78, axiom, (![A, B, C]: ~(((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(![D]: (m1_subset_1(D, k3_zfmisc_1(A, B, C)) => (D = k3_mcart_1(k5_mcart_1(A, B, C, D), k6_mcart_1(A, B, C, D), k7_mcart_1(A, B, C, D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_mcart_1)).
% 3.51/1.57  tff(f_62, axiom, (![A, B, C, D, E, F]: ((k3_mcart_1(A, B, C) = k3_mcart_1(D, E, F)) => (((A = D) & (B = E)) & (C = F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_mcart_1)).
% 3.51/1.57  tff(c_28, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.51/1.57  tff(c_26, plain, (k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.51/1.57  tff(c_24, plain, (k1_xboole_0!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.51/1.57  tff(c_22, plain, (k7_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_8')!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.51/1.57  tff(c_32, plain, (m1_subset_1('#skF_8', k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.51/1.57  tff(c_12, plain, (![A_7, B_8, C_9, D_25]: (m1_subset_1('#skF_1'(A_7, B_8, C_9, D_25), A_7) | ~m1_subset_1(D_25, k3_zfmisc_1(A_7, B_8, C_9)) | k1_xboole_0=C_9 | k1_xboole_0=B_8 | k1_xboole_0=A_7)), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.51/1.57  tff(c_8, plain, (![A_7, B_8, C_9, D_25]: (m1_subset_1('#skF_3'(A_7, B_8, C_9, D_25), C_9) | ~m1_subset_1(D_25, k3_zfmisc_1(A_7, B_8, C_9)) | k1_xboole_0=C_9 | k1_xboole_0=B_8 | k1_xboole_0=A_7)), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.51/1.57  tff(c_10, plain, (![A_7, B_8, C_9, D_25]: (m1_subset_1('#skF_2'(A_7, B_8, C_9, D_25), B_8) | ~m1_subset_1(D_25, k3_zfmisc_1(A_7, B_8, C_9)) | k1_xboole_0=C_9 | k1_xboole_0=B_8 | k1_xboole_0=A_7)), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.51/1.57  tff(c_200, plain, (![A_158, B_159, C_160, D_161]: (k3_mcart_1('#skF_1'(A_158, B_159, C_160, D_161), '#skF_2'(A_158, B_159, C_160, D_161), '#skF_3'(A_158, B_159, C_160, D_161))=D_161 | ~m1_subset_1(D_161, k3_zfmisc_1(A_158, B_159, C_160)) | k1_xboole_0=C_160 | k1_xboole_0=B_159 | k1_xboole_0=A_158)), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.51/1.57  tff(c_30, plain, (![H_61, F_55, G_59]: (H_61='#skF_7' | k3_mcart_1(F_55, G_59, H_61)!='#skF_8' | ~m1_subset_1(H_61, '#skF_6') | ~m1_subset_1(G_59, '#skF_5') | ~m1_subset_1(F_55, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.51/1.57  tff(c_265, plain, (![A_162, B_163, C_164, D_165]: ('#skF_3'(A_162, B_163, C_164, D_165)='#skF_7' | D_165!='#skF_8' | ~m1_subset_1('#skF_3'(A_162, B_163, C_164, D_165), '#skF_6') | ~m1_subset_1('#skF_2'(A_162, B_163, C_164, D_165), '#skF_5') | ~m1_subset_1('#skF_1'(A_162, B_163, C_164, D_165), '#skF_4') | ~m1_subset_1(D_165, k3_zfmisc_1(A_162, B_163, C_164)) | k1_xboole_0=C_164 | k1_xboole_0=B_163 | k1_xboole_0=A_162)), inference(superposition, [status(thm), theory('equality')], [c_200, c_30])).
% 3.51/1.57  tff(c_269, plain, (![A_7, C_9, D_25]: ('#skF_3'(A_7, '#skF_5', C_9, D_25)='#skF_7' | D_25!='#skF_8' | ~m1_subset_1('#skF_3'(A_7, '#skF_5', C_9, D_25), '#skF_6') | ~m1_subset_1('#skF_1'(A_7, '#skF_5', C_9, D_25), '#skF_4') | ~m1_subset_1(D_25, k3_zfmisc_1(A_7, '#skF_5', C_9)) | k1_xboole_0=C_9 | k1_xboole_0='#skF_5' | k1_xboole_0=A_7)), inference(resolution, [status(thm)], [c_10, c_265])).
% 3.51/1.57  tff(c_405, plain, (![A_206, C_207, D_208]: ('#skF_3'(A_206, '#skF_5', C_207, D_208)='#skF_7' | D_208!='#skF_8' | ~m1_subset_1('#skF_3'(A_206, '#skF_5', C_207, D_208), '#skF_6') | ~m1_subset_1('#skF_1'(A_206, '#skF_5', C_207, D_208), '#skF_4') | ~m1_subset_1(D_208, k3_zfmisc_1(A_206, '#skF_5', C_207)) | k1_xboole_0=C_207 | k1_xboole_0=A_206)), inference(negUnitSimplification, [status(thm)], [c_26, c_26, c_269])).
% 3.51/1.57  tff(c_409, plain, (![A_7, D_25]: ('#skF_3'(A_7, '#skF_5', '#skF_6', D_25)='#skF_7' | D_25!='#skF_8' | ~m1_subset_1('#skF_1'(A_7, '#skF_5', '#skF_6', D_25), '#skF_4') | ~m1_subset_1(D_25, k3_zfmisc_1(A_7, '#skF_5', '#skF_6')) | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k1_xboole_0=A_7)), inference(resolution, [status(thm)], [c_8, c_405])).
% 3.51/1.57  tff(c_442, plain, (![A_227, D_228]: ('#skF_3'(A_227, '#skF_5', '#skF_6', D_228)='#skF_7' | D_228!='#skF_8' | ~m1_subset_1('#skF_1'(A_227, '#skF_5', '#skF_6', D_228), '#skF_4') | ~m1_subset_1(D_228, k3_zfmisc_1(A_227, '#skF_5', '#skF_6')) | k1_xboole_0=A_227)), inference(negUnitSimplification, [status(thm)], [c_26, c_24, c_24, c_409])).
% 3.51/1.57  tff(c_446, plain, (![D_25]: ('#skF_3'('#skF_4', '#skF_5', '#skF_6', D_25)='#skF_7' | D_25!='#skF_8' | ~m1_subset_1(D_25, k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6')) | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4')), inference(resolution, [status(thm)], [c_12, c_442])).
% 3.51/1.57  tff(c_451, plain, (![D_229]: ('#skF_3'('#skF_4', '#skF_5', '#skF_6', D_229)='#skF_7' | D_229!='#skF_8' | ~m1_subset_1(D_229, k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6')))), inference(negUnitSimplification, [status(thm)], [c_28, c_26, c_24, c_28, c_446])).
% 3.51/1.57  tff(c_470, plain, ('#skF_3'('#skF_4', '#skF_5', '#skF_6', '#skF_8')='#skF_7'), inference(resolution, [status(thm)], [c_32, c_451])).
% 3.51/1.57  tff(c_6, plain, (![A_7, B_8, C_9, D_25]: (k3_mcart_1('#skF_1'(A_7, B_8, C_9, D_25), '#skF_2'(A_7, B_8, C_9, D_25), '#skF_3'(A_7, B_8, C_9, D_25))=D_25 | ~m1_subset_1(D_25, k3_zfmisc_1(A_7, B_8, C_9)) | k1_xboole_0=C_9 | k1_xboole_0=B_8 | k1_xboole_0=A_7)), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.51/1.57  tff(c_477, plain, (k3_mcart_1('#skF_1'('#skF_4', '#skF_5', '#skF_6', '#skF_8'), '#skF_2'('#skF_4', '#skF_5', '#skF_6', '#skF_8'), '#skF_7')='#skF_8' | ~m1_subset_1('#skF_8', k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6')) | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_470, c_6])).
% 3.51/1.57  tff(c_488, plain, (k3_mcart_1('#skF_1'('#skF_4', '#skF_5', '#skF_6', '#skF_8'), '#skF_2'('#skF_4', '#skF_5', '#skF_6', '#skF_8'), '#skF_7')='#skF_8' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_32, c_477])).
% 3.51/1.57  tff(c_489, plain, (k3_mcart_1('#skF_1'('#skF_4', '#skF_5', '#skF_6', '#skF_8'), '#skF_2'('#skF_4', '#skF_5', '#skF_6', '#skF_8'), '#skF_7')='#skF_8'), inference(negUnitSimplification, [status(thm)], [c_28, c_26, c_24, c_488])).
% 3.51/1.57  tff(c_306, plain, (![A_188, B_189, C_190, D_191]: (k3_mcart_1(k5_mcart_1(A_188, B_189, C_190, D_191), k6_mcart_1(A_188, B_189, C_190, D_191), k7_mcart_1(A_188, B_189, C_190, D_191))=D_191 | ~m1_subset_1(D_191, k3_zfmisc_1(A_188, B_189, C_190)) | k1_xboole_0=C_190 | k1_xboole_0=B_189 | k1_xboole_0=A_188)), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.51/1.57  tff(c_14, plain, (![C_39, B_38, A_37, D_40, F_42, E_41]: (F_42=C_39 | k3_mcart_1(D_40, E_41, F_42)!=k3_mcart_1(A_37, B_38, C_39))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.51/1.57  tff(c_370, plain, (![C_190, B_189, D_40, F_42, A_188, E_41, D_191]: (k7_mcart_1(A_188, B_189, C_190, D_191)=F_42 | k3_mcart_1(D_40, E_41, F_42)!=D_191 | ~m1_subset_1(D_191, k3_zfmisc_1(A_188, B_189, C_190)) | k1_xboole_0=C_190 | k1_xboole_0=B_189 | k1_xboole_0=A_188)), inference(superposition, [status(thm), theory('equality')], [c_306, c_14])).
% 3.51/1.57  tff(c_790, plain, (![A_303, B_304, C_305, D_306]: (k7_mcart_1(A_303, B_304, C_305, D_306)='#skF_7' | D_306!='#skF_8' | ~m1_subset_1(D_306, k3_zfmisc_1(A_303, B_304, C_305)) | k1_xboole_0=C_305 | k1_xboole_0=B_304 | k1_xboole_0=A_303)), inference(superposition, [status(thm), theory('equality')], [c_489, c_370])).
% 3.51/1.57  tff(c_808, plain, (k7_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_8')='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_32, c_790])).
% 3.51/1.57  tff(c_815, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28, c_26, c_24, c_22, c_808])).
% 3.51/1.57  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.51/1.57  
% 3.51/1.57  Inference rules
% 3.51/1.57  ----------------------
% 3.51/1.57  #Ref     : 13
% 3.51/1.57  #Sup     : 208
% 3.51/1.57  #Fact    : 0
% 3.51/1.57  #Define  : 0
% 3.51/1.57  #Split   : 1
% 3.51/1.57  #Chain   : 0
% 3.51/1.57  #Close   : 0
% 3.51/1.57  
% 3.51/1.57  Ordering : KBO
% 3.51/1.57  
% 3.51/1.57  Simplification rules
% 3.51/1.57  ----------------------
% 3.51/1.57  #Subsume      : 47
% 3.51/1.57  #Demod        : 38
% 3.51/1.57  #Tautology    : 34
% 3.51/1.57  #SimpNegUnit  : 8
% 3.51/1.57  #BackRed      : 0
% 3.51/1.57  
% 3.51/1.57  #Partial instantiations: 0
% 3.51/1.57  #Strategies tried      : 1
% 3.51/1.57  
% 3.51/1.57  Timing (in seconds)
% 3.51/1.57  ----------------------
% 3.51/1.57  Preprocessing        : 0.31
% 3.51/1.57  Parsing              : 0.16
% 3.51/1.57  CNF conversion       : 0.02
% 3.51/1.57  Main loop            : 0.46
% 3.51/1.57  Inferencing          : 0.16
% 3.51/1.57  Reduction            : 0.10
% 3.51/1.57  Demodulation         : 0.07
% 3.51/1.57  BG Simplification    : 0.02
% 3.51/1.57  Subsumption          : 0.15
% 3.51/1.57  Abstraction          : 0.03
% 3.51/1.57  MUC search           : 0.00
% 3.51/1.57  Cooper               : 0.00
% 3.51/1.57  Total                : 0.79
% 3.51/1.57  Index Insertion      : 0.00
% 3.51/1.57  Index Deletion       : 0.00
% 3.51/1.57  Index Matching       : 0.00
% 3.51/1.57  BG Taut test         : 0.00
%------------------------------------------------------------------------------
