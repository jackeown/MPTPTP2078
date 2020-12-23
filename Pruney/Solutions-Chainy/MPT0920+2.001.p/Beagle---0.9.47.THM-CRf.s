%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:16 EST 2020

% Result     : Theorem 11.68s
% Output     : CNFRefutation 11.68s
% Verified   : 
% Statistics : Number of formulae       :   54 (  60 expanded)
%              Number of leaves         :   31 (  37 expanded)
%              Depth                    :   12
%              Number of atoms          :  117 ( 189 expanded)
%              Number of equality atoms :   63 ( 105 expanded)
%              Maximal formula depth    :   19 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_subset_1 > k9_mcart_1 > k8_mcart_1 > k11_mcart_1 > k10_mcart_1 > k4_zfmisc_1 > k4_mcart_1 > k3_zfmisc_1 > k3_mcart_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_mcart_1 > k1_xboole_0 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_8 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k10_mcart_1,type,(
    k10_mcart_1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_mcart_1,type,(
    k3_mcart_1: ( $i * $i * $i ) > $i )).

tff(k4_zfmisc_1,type,(
    k4_zfmisc_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k11_mcart_1,type,(
    k11_mcart_1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k3_zfmisc_1,type,(
    k3_zfmisc_1: ( $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff(k8_mcart_1,type,(
    k8_mcart_1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff(k9_mcart_1,type,(
    k9_mcart_1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k4_mcart_1,type,(
    k4_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_121,negated_conjecture,(
    ~ ! [A,B,C,D,E,F] :
        ( m1_subset_1(F,k4_zfmisc_1(A,B,C,D))
       => ( ! [G] :
              ( m1_subset_1(G,A)
             => ! [H] :
                  ( m1_subset_1(H,B)
                 => ! [I] :
                      ( m1_subset_1(I,C)
                     => ! [J] :
                          ( m1_subset_1(J,D)
                         => ( F = k4_mcart_1(G,H,I,J)
                           => E = H ) ) ) ) )
         => ( A = k1_xboole_0
            | B = k1_xboole_0
            | C = k1_xboole_0
            | D = k1_xboole_0
            | E = k9_mcart_1(A,B,C,D,F) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_mcart_1)).

tff(f_48,axiom,(
    ! [A,B,C,D,E] :
      ( m1_subset_1(E,k4_zfmisc_1(A,B,C,D))
     => m1_subset_1(k10_mcart_1(A,B,C,D,E),C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k10_mcart_1)).

tff(f_52,axiom,(
    ! [A,B,C,D,E] :
      ( m1_subset_1(E,k4_zfmisc_1(A,B,C,D))
     => m1_subset_1(k11_mcart_1(A,B,C,D,E),D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k11_mcart_1)).

tff(f_56,axiom,(
    ! [A,B,C,D,E] :
      ( m1_subset_1(E,k4_zfmisc_1(A,B,C,D))
     => m1_subset_1(k8_mcart_1(A,B,C,D,E),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_mcart_1)).

tff(f_60,axiom,(
    ! [A,B,C,D,E] :
      ( m1_subset_1(E,k4_zfmisc_1(A,B,C,D))
     => m1_subset_1(k9_mcart_1(A,B,C,D,E),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k9_mcart_1)).

tff(f_88,axiom,(
    ! [A,B,C,D] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & C != k1_xboole_0
        & D != k1_xboole_0
        & ~ ! [E] :
              ( m1_subset_1(E,k4_zfmisc_1(A,B,C,D))
             => E = k4_mcart_1(k8_mcart_1(A,B,C,D,E),k9_mcart_1(A,B,C,D,E),k10_mcart_1(A,B,C,D,E),k11_mcart_1(A,B,C,D,E)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_mcart_1)).

tff(c_34,plain,(
    k9_mcart_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_8') != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_46,plain,(
    m1_subset_1('#skF_8',k4_zfmisc_1('#skF_3','#skF_4','#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_38,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_16,plain,(
    ! [D_39,A_36,E_40,C_38,B_37] :
      ( m1_subset_1(k10_mcart_1(A_36,B_37,C_38,D_39,E_40),C_38)
      | ~ m1_subset_1(E_40,k4_zfmisc_1(A_36,B_37,C_38,D_39)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_36,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_18,plain,(
    ! [D_44,C_43,A_41,B_42,E_45] :
      ( m1_subset_1(k11_mcart_1(A_41,B_42,C_43,D_44,E_45),D_44)
      | ~ m1_subset_1(E_45,k4_zfmisc_1(A_41,B_42,C_43,D_44)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_42,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_20,plain,(
    ! [A_46,E_50,B_47,C_48,D_49] :
      ( m1_subset_1(k8_mcart_1(A_46,B_47,C_48,D_49,E_50),A_46)
      | ~ m1_subset_1(E_50,k4_zfmisc_1(A_46,B_47,C_48,D_49)) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_40,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_22,plain,(
    ! [B_52,E_55,C_53,D_54,A_51] :
      ( m1_subset_1(k9_mcart_1(A_51,B_52,C_53,D_54,E_55),B_52)
      | ~ m1_subset_1(E_55,k4_zfmisc_1(A_51,B_52,C_53,D_54)) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_533,plain,(
    ! [A_235,B_234,D_233,C_232,E_231] :
      ( k4_mcart_1(k8_mcart_1(A_235,B_234,C_232,D_233,E_231),k9_mcart_1(A_235,B_234,C_232,D_233,E_231),k10_mcart_1(A_235,B_234,C_232,D_233,E_231),k11_mcart_1(A_235,B_234,C_232,D_233,E_231)) = E_231
      | ~ m1_subset_1(E_231,k4_zfmisc_1(A_235,B_234,C_232,D_233))
      | k1_xboole_0 = D_233
      | k1_xboole_0 = C_232
      | k1_xboole_0 = B_234
      | k1_xboole_0 = A_235 ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_44,plain,(
    ! [H_92,G_84,I_96,J_98] :
      ( H_92 = '#skF_7'
      | k4_mcart_1(G_84,H_92,I_96,J_98) != '#skF_8'
      | ~ m1_subset_1(J_98,'#skF_6')
      | ~ m1_subset_1(I_96,'#skF_5')
      | ~ m1_subset_1(H_92,'#skF_4')
      | ~ m1_subset_1(G_84,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_613,plain,(
    ! [B_249,C_248,A_250,E_247,D_251] :
      ( k9_mcart_1(A_250,B_249,C_248,D_251,E_247) = '#skF_7'
      | E_247 != '#skF_8'
      | ~ m1_subset_1(k11_mcart_1(A_250,B_249,C_248,D_251,E_247),'#skF_6')
      | ~ m1_subset_1(k10_mcart_1(A_250,B_249,C_248,D_251,E_247),'#skF_5')
      | ~ m1_subset_1(k9_mcart_1(A_250,B_249,C_248,D_251,E_247),'#skF_4')
      | ~ m1_subset_1(k8_mcart_1(A_250,B_249,C_248,D_251,E_247),'#skF_3')
      | ~ m1_subset_1(E_247,k4_zfmisc_1(A_250,B_249,C_248,D_251))
      | k1_xboole_0 = D_251
      | k1_xboole_0 = C_248
      | k1_xboole_0 = B_249
      | k1_xboole_0 = A_250 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_533,c_44])).

tff(c_617,plain,(
    ! [A_51,C_53,D_54,E_55] :
      ( k9_mcart_1(A_51,'#skF_4',C_53,D_54,E_55) = '#skF_7'
      | E_55 != '#skF_8'
      | ~ m1_subset_1(k11_mcart_1(A_51,'#skF_4',C_53,D_54,E_55),'#skF_6')
      | ~ m1_subset_1(k10_mcart_1(A_51,'#skF_4',C_53,D_54,E_55),'#skF_5')
      | ~ m1_subset_1(k8_mcart_1(A_51,'#skF_4',C_53,D_54,E_55),'#skF_3')
      | k1_xboole_0 = D_54
      | k1_xboole_0 = C_53
      | k1_xboole_0 = '#skF_4'
      | k1_xboole_0 = A_51
      | ~ m1_subset_1(E_55,k4_zfmisc_1(A_51,'#skF_4',C_53,D_54)) ) ),
    inference(resolution,[status(thm)],[c_22,c_613])).

tff(c_788,plain,(
    ! [A_281,C_282,D_283,E_284] :
      ( k9_mcart_1(A_281,'#skF_4',C_282,D_283,E_284) = '#skF_7'
      | E_284 != '#skF_8'
      | ~ m1_subset_1(k11_mcart_1(A_281,'#skF_4',C_282,D_283,E_284),'#skF_6')
      | ~ m1_subset_1(k10_mcart_1(A_281,'#skF_4',C_282,D_283,E_284),'#skF_5')
      | ~ m1_subset_1(k8_mcart_1(A_281,'#skF_4',C_282,D_283,E_284),'#skF_3')
      | k1_xboole_0 = D_283
      | k1_xboole_0 = C_282
      | k1_xboole_0 = A_281
      | ~ m1_subset_1(E_284,k4_zfmisc_1(A_281,'#skF_4',C_282,D_283)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_617])).

tff(c_792,plain,(
    ! [C_48,D_49,E_50] :
      ( k9_mcart_1('#skF_3','#skF_4',C_48,D_49,E_50) = '#skF_7'
      | E_50 != '#skF_8'
      | ~ m1_subset_1(k11_mcart_1('#skF_3','#skF_4',C_48,D_49,E_50),'#skF_6')
      | ~ m1_subset_1(k10_mcart_1('#skF_3','#skF_4',C_48,D_49,E_50),'#skF_5')
      | k1_xboole_0 = D_49
      | k1_xboole_0 = C_48
      | k1_xboole_0 = '#skF_3'
      | ~ m1_subset_1(E_50,k4_zfmisc_1('#skF_3','#skF_4',C_48,D_49)) ) ),
    inference(resolution,[status(thm)],[c_20,c_788])).

tff(c_1601,plain,(
    ! [C_344,D_345,E_346] :
      ( k9_mcart_1('#skF_3','#skF_4',C_344,D_345,E_346) = '#skF_7'
      | E_346 != '#skF_8'
      | ~ m1_subset_1(k11_mcart_1('#skF_3','#skF_4',C_344,D_345,E_346),'#skF_6')
      | ~ m1_subset_1(k10_mcart_1('#skF_3','#skF_4',C_344,D_345,E_346),'#skF_5')
      | k1_xboole_0 = D_345
      | k1_xboole_0 = C_344
      | ~ m1_subset_1(E_346,k4_zfmisc_1('#skF_3','#skF_4',C_344,D_345)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_792])).

tff(c_1605,plain,(
    ! [C_43,E_45] :
      ( k9_mcart_1('#skF_3','#skF_4',C_43,'#skF_6',E_45) = '#skF_7'
      | E_45 != '#skF_8'
      | ~ m1_subset_1(k10_mcart_1('#skF_3','#skF_4',C_43,'#skF_6',E_45),'#skF_5')
      | k1_xboole_0 = '#skF_6'
      | k1_xboole_0 = C_43
      | ~ m1_subset_1(E_45,k4_zfmisc_1('#skF_3','#skF_4',C_43,'#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_18,c_1601])).

tff(c_37606,plain,(
    ! [C_22900,E_22901] :
      ( k9_mcart_1('#skF_3','#skF_4',C_22900,'#skF_6',E_22901) = '#skF_7'
      | E_22901 != '#skF_8'
      | ~ m1_subset_1(k10_mcart_1('#skF_3','#skF_4',C_22900,'#skF_6',E_22901),'#skF_5')
      | k1_xboole_0 = C_22900
      | ~ m1_subset_1(E_22901,k4_zfmisc_1('#skF_3','#skF_4',C_22900,'#skF_6')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_1605])).

tff(c_38399,plain,(
    ! [E_40] :
      ( k9_mcart_1('#skF_3','#skF_4','#skF_5','#skF_6',E_40) = '#skF_7'
      | E_40 != '#skF_8'
      | k1_xboole_0 = '#skF_5'
      | ~ m1_subset_1(E_40,k4_zfmisc_1('#skF_3','#skF_4','#skF_5','#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_16,c_37606])).

tff(c_62866,plain,(
    ! [E_30314] :
      ( k9_mcart_1('#skF_3','#skF_4','#skF_5','#skF_6',E_30314) = '#skF_7'
      | E_30314 != '#skF_8'
      | ~ m1_subset_1(E_30314,k4_zfmisc_1('#skF_3','#skF_4','#skF_5','#skF_6')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_38399])).

tff(c_62885,plain,(
    k9_mcart_1('#skF_3','#skF_4','#skF_5','#skF_6','#skF_8') = '#skF_7' ),
    inference(resolution,[status(thm)],[c_46,c_62866])).

tff(c_62893,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_62885])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:17:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 11.68/4.67  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.68/4.67  
% 11.68/4.67  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.68/4.67  %$ m1_subset_1 > k9_mcart_1 > k8_mcart_1 > k11_mcart_1 > k10_mcart_1 > k4_zfmisc_1 > k4_mcart_1 > k3_zfmisc_1 > k3_mcart_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_mcart_1 > k1_xboole_0 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_8 > #skF_4 > #skF_2 > #skF_1
% 11.68/4.67  
% 11.68/4.67  %Foreground sorts:
% 11.68/4.67  
% 11.68/4.67  
% 11.68/4.67  %Background operators:
% 11.68/4.67  
% 11.68/4.67  
% 11.68/4.67  %Foreground operators:
% 11.68/4.67  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 11.68/4.67  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 11.68/4.67  tff(k10_mcart_1, type, k10_mcart_1: ($i * $i * $i * $i * $i) > $i).
% 11.68/4.67  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 11.68/4.67  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 11.68/4.67  tff(k4_zfmisc_1, type, k4_zfmisc_1: ($i * $i * $i * $i) > $i).
% 11.68/4.67  tff('#skF_7', type, '#skF_7': $i).
% 11.68/4.67  tff('#skF_5', type, '#skF_5': $i).
% 11.68/4.67  tff(k11_mcart_1, type, k11_mcart_1: ($i * $i * $i * $i * $i) > $i).
% 11.68/4.67  tff('#skF_6', type, '#skF_6': $i).
% 11.68/4.67  tff('#skF_3', type, '#skF_3': $i).
% 11.68/4.67  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 11.68/4.67  tff('#skF_8', type, '#skF_8': $i).
% 11.68/4.67  tff(k8_mcart_1, type, k8_mcart_1: ($i * $i * $i * $i * $i) > $i).
% 11.68/4.67  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 11.68/4.67  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 11.68/4.67  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 11.68/4.67  tff('#skF_4', type, '#skF_4': $i).
% 11.68/4.67  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 11.68/4.67  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 11.68/4.67  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 11.68/4.67  tff(k9_mcart_1, type, k9_mcart_1: ($i * $i * $i * $i * $i) > $i).
% 11.68/4.67  tff(k4_mcart_1, type, k4_mcart_1: ($i * $i * $i * $i) > $i).
% 11.68/4.67  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 11.68/4.67  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 11.68/4.67  
% 11.68/4.68  tff(f_121, negated_conjecture, ~(![A, B, C, D, E, F]: (m1_subset_1(F, k4_zfmisc_1(A, B, C, D)) => ((![G]: (m1_subset_1(G, A) => (![H]: (m1_subset_1(H, B) => (![I]: (m1_subset_1(I, C) => (![J]: (m1_subset_1(J, D) => ((F = k4_mcart_1(G, H, I, J)) => (E = H)))))))))) => (((((A = k1_xboole_0) | (B = k1_xboole_0)) | (C = k1_xboole_0)) | (D = k1_xboole_0)) | (E = k9_mcart_1(A, B, C, D, F)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t80_mcart_1)).
% 11.68/4.68  tff(f_48, axiom, (![A, B, C, D, E]: (m1_subset_1(E, k4_zfmisc_1(A, B, C, D)) => m1_subset_1(k10_mcart_1(A, B, C, D, E), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k10_mcart_1)).
% 11.68/4.68  tff(f_52, axiom, (![A, B, C, D, E]: (m1_subset_1(E, k4_zfmisc_1(A, B, C, D)) => m1_subset_1(k11_mcart_1(A, B, C, D, E), D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k11_mcart_1)).
% 11.68/4.68  tff(f_56, axiom, (![A, B, C, D, E]: (m1_subset_1(E, k4_zfmisc_1(A, B, C, D)) => m1_subset_1(k8_mcart_1(A, B, C, D, E), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k8_mcart_1)).
% 11.68/4.68  tff(f_60, axiom, (![A, B, C, D, E]: (m1_subset_1(E, k4_zfmisc_1(A, B, C, D)) => m1_subset_1(k9_mcart_1(A, B, C, D, E), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k9_mcart_1)).
% 11.68/4.68  tff(f_88, axiom, (![A, B, C, D]: ~((((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(D = k1_xboole_0)) & ~(![E]: (m1_subset_1(E, k4_zfmisc_1(A, B, C, D)) => (E = k4_mcart_1(k8_mcart_1(A, B, C, D, E), k9_mcart_1(A, B, C, D, E), k10_mcart_1(A, B, C, D, E), k11_mcart_1(A, B, C, D, E))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_mcart_1)).
% 11.68/4.68  tff(c_34, plain, (k9_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_8')!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_121])).
% 11.68/4.68  tff(c_46, plain, (m1_subset_1('#skF_8', k4_zfmisc_1('#skF_3', '#skF_4', '#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_121])).
% 11.68/4.68  tff(c_38, plain, (k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_121])).
% 11.68/4.68  tff(c_16, plain, (![D_39, A_36, E_40, C_38, B_37]: (m1_subset_1(k10_mcart_1(A_36, B_37, C_38, D_39, E_40), C_38) | ~m1_subset_1(E_40, k4_zfmisc_1(A_36, B_37, C_38, D_39)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 11.68/4.68  tff(c_36, plain, (k1_xboole_0!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_121])).
% 11.68/4.68  tff(c_18, plain, (![D_44, C_43, A_41, B_42, E_45]: (m1_subset_1(k11_mcart_1(A_41, B_42, C_43, D_44, E_45), D_44) | ~m1_subset_1(E_45, k4_zfmisc_1(A_41, B_42, C_43, D_44)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 11.68/4.68  tff(c_42, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_121])).
% 11.68/4.68  tff(c_20, plain, (![A_46, E_50, B_47, C_48, D_49]: (m1_subset_1(k8_mcart_1(A_46, B_47, C_48, D_49, E_50), A_46) | ~m1_subset_1(E_50, k4_zfmisc_1(A_46, B_47, C_48, D_49)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 11.68/4.68  tff(c_40, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_121])).
% 11.68/4.68  tff(c_22, plain, (![B_52, E_55, C_53, D_54, A_51]: (m1_subset_1(k9_mcart_1(A_51, B_52, C_53, D_54, E_55), B_52) | ~m1_subset_1(E_55, k4_zfmisc_1(A_51, B_52, C_53, D_54)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 11.68/4.68  tff(c_533, plain, (![A_235, B_234, D_233, C_232, E_231]: (k4_mcart_1(k8_mcart_1(A_235, B_234, C_232, D_233, E_231), k9_mcart_1(A_235, B_234, C_232, D_233, E_231), k10_mcart_1(A_235, B_234, C_232, D_233, E_231), k11_mcart_1(A_235, B_234, C_232, D_233, E_231))=E_231 | ~m1_subset_1(E_231, k4_zfmisc_1(A_235, B_234, C_232, D_233)) | k1_xboole_0=D_233 | k1_xboole_0=C_232 | k1_xboole_0=B_234 | k1_xboole_0=A_235)), inference(cnfTransformation, [status(thm)], [f_88])).
% 11.68/4.68  tff(c_44, plain, (![H_92, G_84, I_96, J_98]: (H_92='#skF_7' | k4_mcart_1(G_84, H_92, I_96, J_98)!='#skF_8' | ~m1_subset_1(J_98, '#skF_6') | ~m1_subset_1(I_96, '#skF_5') | ~m1_subset_1(H_92, '#skF_4') | ~m1_subset_1(G_84, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_121])).
% 11.68/4.68  tff(c_613, plain, (![B_249, C_248, A_250, E_247, D_251]: (k9_mcart_1(A_250, B_249, C_248, D_251, E_247)='#skF_7' | E_247!='#skF_8' | ~m1_subset_1(k11_mcart_1(A_250, B_249, C_248, D_251, E_247), '#skF_6') | ~m1_subset_1(k10_mcart_1(A_250, B_249, C_248, D_251, E_247), '#skF_5') | ~m1_subset_1(k9_mcart_1(A_250, B_249, C_248, D_251, E_247), '#skF_4') | ~m1_subset_1(k8_mcart_1(A_250, B_249, C_248, D_251, E_247), '#skF_3') | ~m1_subset_1(E_247, k4_zfmisc_1(A_250, B_249, C_248, D_251)) | k1_xboole_0=D_251 | k1_xboole_0=C_248 | k1_xboole_0=B_249 | k1_xboole_0=A_250)), inference(superposition, [status(thm), theory('equality')], [c_533, c_44])).
% 11.68/4.68  tff(c_617, plain, (![A_51, C_53, D_54, E_55]: (k9_mcart_1(A_51, '#skF_4', C_53, D_54, E_55)='#skF_7' | E_55!='#skF_8' | ~m1_subset_1(k11_mcart_1(A_51, '#skF_4', C_53, D_54, E_55), '#skF_6') | ~m1_subset_1(k10_mcart_1(A_51, '#skF_4', C_53, D_54, E_55), '#skF_5') | ~m1_subset_1(k8_mcart_1(A_51, '#skF_4', C_53, D_54, E_55), '#skF_3') | k1_xboole_0=D_54 | k1_xboole_0=C_53 | k1_xboole_0='#skF_4' | k1_xboole_0=A_51 | ~m1_subset_1(E_55, k4_zfmisc_1(A_51, '#skF_4', C_53, D_54)))), inference(resolution, [status(thm)], [c_22, c_613])).
% 11.68/4.68  tff(c_788, plain, (![A_281, C_282, D_283, E_284]: (k9_mcart_1(A_281, '#skF_4', C_282, D_283, E_284)='#skF_7' | E_284!='#skF_8' | ~m1_subset_1(k11_mcart_1(A_281, '#skF_4', C_282, D_283, E_284), '#skF_6') | ~m1_subset_1(k10_mcart_1(A_281, '#skF_4', C_282, D_283, E_284), '#skF_5') | ~m1_subset_1(k8_mcart_1(A_281, '#skF_4', C_282, D_283, E_284), '#skF_3') | k1_xboole_0=D_283 | k1_xboole_0=C_282 | k1_xboole_0=A_281 | ~m1_subset_1(E_284, k4_zfmisc_1(A_281, '#skF_4', C_282, D_283)))), inference(negUnitSimplification, [status(thm)], [c_40, c_617])).
% 11.68/4.68  tff(c_792, plain, (![C_48, D_49, E_50]: (k9_mcart_1('#skF_3', '#skF_4', C_48, D_49, E_50)='#skF_7' | E_50!='#skF_8' | ~m1_subset_1(k11_mcart_1('#skF_3', '#skF_4', C_48, D_49, E_50), '#skF_6') | ~m1_subset_1(k10_mcart_1('#skF_3', '#skF_4', C_48, D_49, E_50), '#skF_5') | k1_xboole_0=D_49 | k1_xboole_0=C_48 | k1_xboole_0='#skF_3' | ~m1_subset_1(E_50, k4_zfmisc_1('#skF_3', '#skF_4', C_48, D_49)))), inference(resolution, [status(thm)], [c_20, c_788])).
% 11.68/4.68  tff(c_1601, plain, (![C_344, D_345, E_346]: (k9_mcart_1('#skF_3', '#skF_4', C_344, D_345, E_346)='#skF_7' | E_346!='#skF_8' | ~m1_subset_1(k11_mcart_1('#skF_3', '#skF_4', C_344, D_345, E_346), '#skF_6') | ~m1_subset_1(k10_mcart_1('#skF_3', '#skF_4', C_344, D_345, E_346), '#skF_5') | k1_xboole_0=D_345 | k1_xboole_0=C_344 | ~m1_subset_1(E_346, k4_zfmisc_1('#skF_3', '#skF_4', C_344, D_345)))), inference(negUnitSimplification, [status(thm)], [c_42, c_792])).
% 11.68/4.68  tff(c_1605, plain, (![C_43, E_45]: (k9_mcart_1('#skF_3', '#skF_4', C_43, '#skF_6', E_45)='#skF_7' | E_45!='#skF_8' | ~m1_subset_1(k10_mcart_1('#skF_3', '#skF_4', C_43, '#skF_6', E_45), '#skF_5') | k1_xboole_0='#skF_6' | k1_xboole_0=C_43 | ~m1_subset_1(E_45, k4_zfmisc_1('#skF_3', '#skF_4', C_43, '#skF_6')))), inference(resolution, [status(thm)], [c_18, c_1601])).
% 11.68/4.68  tff(c_37606, plain, (![C_22900, E_22901]: (k9_mcart_1('#skF_3', '#skF_4', C_22900, '#skF_6', E_22901)='#skF_7' | E_22901!='#skF_8' | ~m1_subset_1(k10_mcart_1('#skF_3', '#skF_4', C_22900, '#skF_6', E_22901), '#skF_5') | k1_xboole_0=C_22900 | ~m1_subset_1(E_22901, k4_zfmisc_1('#skF_3', '#skF_4', C_22900, '#skF_6')))), inference(negUnitSimplification, [status(thm)], [c_36, c_1605])).
% 11.68/4.68  tff(c_38399, plain, (![E_40]: (k9_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_6', E_40)='#skF_7' | E_40!='#skF_8' | k1_xboole_0='#skF_5' | ~m1_subset_1(E_40, k4_zfmisc_1('#skF_3', '#skF_4', '#skF_5', '#skF_6')))), inference(resolution, [status(thm)], [c_16, c_37606])).
% 11.68/4.68  tff(c_62866, plain, (![E_30314]: (k9_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_6', E_30314)='#skF_7' | E_30314!='#skF_8' | ~m1_subset_1(E_30314, k4_zfmisc_1('#skF_3', '#skF_4', '#skF_5', '#skF_6')))), inference(negUnitSimplification, [status(thm)], [c_38, c_38399])).
% 11.68/4.68  tff(c_62885, plain, (k9_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_6', '#skF_8')='#skF_7'), inference(resolution, [status(thm)], [c_46, c_62866])).
% 11.68/4.68  tff(c_62893, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34, c_62885])).
% 11.68/4.68  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.68/4.68  
% 11.68/4.68  Inference rules
% 11.68/4.68  ----------------------
% 11.68/4.68  #Ref     : 1
% 11.68/4.68  #Sup     : 5016
% 11.68/4.68  #Fact    : 20
% 11.68/4.68  #Define  : 0
% 11.68/4.68  #Split   : 1
% 11.68/4.68  #Chain   : 0
% 11.68/4.68  #Close   : 0
% 11.68/4.68  
% 11.68/4.68  Ordering : KBO
% 11.68/4.68  
% 11.68/4.68  Simplification rules
% 11.68/4.68  ----------------------
% 11.68/4.68  #Subsume      : 1461
% 11.68/4.68  #Demod        : 930
% 11.68/4.68  #Tautology    : 155
% 11.68/4.68  #SimpNegUnit  : 5
% 11.68/4.68  #BackRed      : 0
% 11.68/4.68  
% 11.68/4.68  #Partial instantiations: 14280
% 11.68/4.68  #Strategies tried      : 1
% 11.68/4.68  
% 11.68/4.68  Timing (in seconds)
% 11.68/4.68  ----------------------
% 11.68/4.69  Preprocessing        : 0.34
% 11.68/4.69  Parsing              : 0.18
% 11.68/4.69  CNF conversion       : 0.03
% 11.68/4.69  Main loop            : 3.58
% 11.68/4.69  Inferencing          : 1.90
% 11.68/4.69  Reduction            : 0.77
% 11.68/4.69  Demodulation         : 0.47
% 11.68/4.69  BG Simplification    : 0.19
% 11.68/4.69  Subsumption          : 0.60
% 11.68/4.69  Abstraction          : 0.24
% 11.68/4.69  MUC search           : 0.00
% 11.68/4.69  Cooper               : 0.00
% 11.68/4.69  Total                : 3.95
% 11.68/4.69  Index Insertion      : 0.00
% 11.68/4.69  Index Deletion       : 0.00
% 11.68/4.69  Index Matching       : 0.00
% 11.68/4.69  BG Taut test         : 0.00
%------------------------------------------------------------------------------
