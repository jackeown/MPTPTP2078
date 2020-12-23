%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:06 EST 2020

% Result     : Theorem 8.08s
% Output     : CNFRefutation 8.08s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 328 expanded)
%              Number of leaves         :   32 ( 134 expanded)
%              Depth                    :   11
%              Number of atoms          :  207 (1220 expanded)
%              Number of equality atoms :   88 ( 690 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > v1_xboole_0 > k7_mcart_1 > k6_mcart_1 > k5_mcart_1 > k3_zfmisc_1 > k3_mcart_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_mcart_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_mcart_1,type,(
    k3_mcart_1: ( $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k7_mcart_1,type,(
    k7_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff(k3_zfmisc_1,type,(
    k3_zfmisc_1: ( $i * $i * $i ) > $i )).

tff(k5_mcart_1,type,(
    k5_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k6_mcart_1,type,(
    k6_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_130,negated_conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_mcart_1)).

tff(f_106,axiom,(
    ! [A,B,C] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & C != k1_xboole_0
        & ~ ! [D] :
              ( m1_subset_1(D,k3_zfmisc_1(A,B,C))
             => ( k5_mcart_1(A,B,C,D) = k1_mcart_1(k1_mcart_1(D))
                & k6_mcart_1(A,B,C,D) = k2_mcart_1(k1_mcart_1(D))
                & k7_mcart_1(A,B,C,D) = k2_mcart_1(D) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_mcart_1)).

tff(f_52,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k3_zfmisc_1(A,B,C))
     => m1_subset_1(k7_mcart_1(A,B,C,D),C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_mcart_1)).

tff(f_86,axiom,(
    ! [A,B,C] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & C != k1_xboole_0
        & ~ ! [D] :
              ( m1_subset_1(D,k3_zfmisc_1(A,B,C))
             => D = k3_mcart_1(k5_mcart_1(A,B,C,D),k6_mcart_1(A,B,C,D),k7_mcart_1(A,B,C,D)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_mcart_1)).

tff(f_48,axiom,(
    ! [A,B,C] : k3_zfmisc_1(A,B,C) = k2_zfmisc_1(k2_zfmisc_1(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_58,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k2_zfmisc_1(B,C))
     => ( r2_hidden(k1_mcart_1(A),B)
        & r2_hidden(k2_mcart_1(A),C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_34,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( ( A != k1_xboole_0
        & B != k1_xboole_0
        & C != k1_xboole_0 )
    <=> k3_zfmisc_1(A,B,C) != k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_mcart_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(c_42,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_40,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_38,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_46,plain,(
    m1_subset_1('#skF_5',k3_zfmisc_1('#skF_1','#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_292,plain,(
    ! [A_106,B_107,C_108,D_109] :
      ( k7_mcart_1(A_106,B_107,C_108,D_109) = k2_mcart_1(D_109)
      | ~ m1_subset_1(D_109,k3_zfmisc_1(A_106,B_107,C_108))
      | k1_xboole_0 = C_108
      | k1_xboole_0 = B_107
      | k1_xboole_0 = A_106 ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_311,plain,
    ( k7_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5') = k2_mcart_1('#skF_5')
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_46,c_292])).

tff(c_327,plain,(
    k7_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5') = k2_mcart_1('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_40,c_38,c_311])).

tff(c_36,plain,(
    k7_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_331,plain,(
    k2_mcart_1('#skF_5') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_327,c_36])).

tff(c_14,plain,(
    ! [A_13,B_14,C_15,D_16] :
      ( m1_subset_1(k7_mcart_1(A_13,B_14,C_15,D_16),C_15)
      | ~ m1_subset_1(D_16,k3_zfmisc_1(A_13,B_14,C_15)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_335,plain,
    ( m1_subset_1(k2_mcart_1('#skF_5'),'#skF_3')
    | ~ m1_subset_1('#skF_5',k3_zfmisc_1('#skF_1','#skF_2','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_327,c_14])).

tff(c_339,plain,(
    m1_subset_1(k2_mcart_1('#skF_5'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_335])).

tff(c_642,plain,(
    ! [A_136,B_137,C_138,D_139] :
      ( k3_mcart_1(k5_mcart_1(A_136,B_137,C_138,D_139),k6_mcart_1(A_136,B_137,C_138,D_139),k7_mcart_1(A_136,B_137,C_138,D_139)) = D_139
      | ~ m1_subset_1(D_139,k3_zfmisc_1(A_136,B_137,C_138))
      | k1_xboole_0 = C_138
      | k1_xboole_0 = B_137
      | k1_xboole_0 = A_136 ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_44,plain,(
    ! [H_46,F_40,G_44] :
      ( H_46 = '#skF_4'
      | k3_mcart_1(F_40,G_44,H_46) != '#skF_5'
      | ~ m1_subset_1(H_46,'#skF_3')
      | ~ m1_subset_1(G_44,'#skF_2')
      | ~ m1_subset_1(F_40,'#skF_1') ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_891,plain,(
    ! [A_159,B_160,C_161,D_162] :
      ( k7_mcart_1(A_159,B_160,C_161,D_162) = '#skF_4'
      | D_162 != '#skF_5'
      | ~ m1_subset_1(k7_mcart_1(A_159,B_160,C_161,D_162),'#skF_3')
      | ~ m1_subset_1(k6_mcart_1(A_159,B_160,C_161,D_162),'#skF_2')
      | ~ m1_subset_1(k5_mcart_1(A_159,B_160,C_161,D_162),'#skF_1')
      | ~ m1_subset_1(D_162,k3_zfmisc_1(A_159,B_160,C_161))
      | k1_xboole_0 = C_161
      | k1_xboole_0 = B_160
      | k1_xboole_0 = A_159 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_642,c_44])).

tff(c_894,plain,
    ( k7_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5') = '#skF_4'
    | ~ m1_subset_1(k2_mcart_1('#skF_5'),'#skF_3')
    | ~ m1_subset_1(k6_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_2')
    | ~ m1_subset_1(k5_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_1')
    | ~ m1_subset_1('#skF_5',k3_zfmisc_1('#skF_1','#skF_2','#skF_3'))
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_327,c_891])).

tff(c_901,plain,
    ( k2_mcart_1('#skF_5') = '#skF_4'
    | ~ m1_subset_1(k6_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_2')
    | ~ m1_subset_1(k5_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_1')
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_339,c_327,c_894])).

tff(c_902,plain,
    ( ~ m1_subset_1(k6_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_2')
    | ~ m1_subset_1(k5_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_40,c_38,c_331,c_901])).

tff(c_1062,plain,(
    ~ m1_subset_1(k5_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_902])).

tff(c_459,plain,(
    ! [A_120,B_121,C_122,D_123] :
      ( k5_mcart_1(A_120,B_121,C_122,D_123) = k1_mcart_1(k1_mcart_1(D_123))
      | ~ m1_subset_1(D_123,k3_zfmisc_1(A_120,B_121,C_122))
      | k1_xboole_0 = C_122
      | k1_xboole_0 = B_121
      | k1_xboole_0 = A_120 ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_486,plain,
    ( k1_mcart_1(k1_mcart_1('#skF_5')) = k5_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5')
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_46,c_459])).

tff(c_504,plain,(
    k1_mcart_1(k1_mcart_1('#skF_5')) = k5_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_40,c_38,c_486])).

tff(c_12,plain,(
    ! [A_10,B_11,C_12] : k2_zfmisc_1(k2_zfmisc_1(A_10,B_11),C_12) = k3_zfmisc_1(A_10,B_11,C_12) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( r2_hidden(A_5,B_6)
      | v1_xboole_0(B_6)
      | ~ m1_subset_1(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_108,plain,(
    ! [A_60,C_61,B_62] :
      ( r2_hidden(k2_mcart_1(A_60),C_61)
      | ~ r2_hidden(A_60,k2_zfmisc_1(B_62,C_61)) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_1509,plain,(
    ! [A_227,C_228,B_229] :
      ( r2_hidden(k2_mcart_1(A_227),C_228)
      | v1_xboole_0(k2_zfmisc_1(B_229,C_228))
      | ~ m1_subset_1(A_227,k2_zfmisc_1(B_229,C_228)) ) ),
    inference(resolution,[status(thm)],[c_8,c_108])).

tff(c_1561,plain,(
    ! [A_227,C_12,A_10,B_11] :
      ( r2_hidden(k2_mcart_1(A_227),C_12)
      | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(A_10,B_11),C_12))
      | ~ m1_subset_1(A_227,k3_zfmisc_1(A_10,B_11,C_12)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_1509])).

tff(c_3181,plain,(
    ! [A_322,C_323,A_324,B_325] :
      ( r2_hidden(k2_mcart_1(A_322),C_323)
      | v1_xboole_0(k3_zfmisc_1(A_324,B_325,C_323))
      | ~ m1_subset_1(A_322,k3_zfmisc_1(A_324,B_325,C_323)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_1561])).

tff(c_3316,plain,
    ( r2_hidden(k2_mcart_1('#skF_5'),'#skF_3')
    | v1_xboole_0(k3_zfmisc_1('#skF_1','#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_46,c_3181])).

tff(c_3320,plain,(
    v1_xboole_0(k3_zfmisc_1('#skF_1','#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_3316])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_93,plain,(
    ! [B_55,A_56] :
      ( ~ v1_xboole_0(B_55)
      | B_55 = A_56
      | ~ v1_xboole_0(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_96,plain,(
    ! [A_56] :
      ( k1_xboole_0 = A_56
      | ~ v1_xboole_0(A_56) ) ),
    inference(resolution,[status(thm)],[c_2,c_93])).

tff(c_3326,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_3320,c_96])).

tff(c_20,plain,(
    ! [A_20,B_21,C_22] :
      ( k3_zfmisc_1(A_20,B_21,C_22) != k1_xboole_0
      | k1_xboole_0 = C_22
      | k1_xboole_0 = B_21
      | k1_xboole_0 = A_20 ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_3365,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_3326,c_20])).

tff(c_3387,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_40,c_38,c_3365])).

tff(c_3389,plain,(
    ~ v1_xboole_0(k3_zfmisc_1('#skF_1','#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_3316])).

tff(c_145,plain,(
    ! [A_69,B_70,C_71] :
      ( r2_hidden(k1_mcart_1(A_69),B_70)
      | ~ r2_hidden(A_69,k2_zfmisc_1(B_70,C_71)) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_749,plain,(
    ! [A_148,A_149,B_150,C_151] :
      ( r2_hidden(k1_mcart_1(A_148),k2_zfmisc_1(A_149,B_150))
      | ~ r2_hidden(A_148,k3_zfmisc_1(A_149,B_150,C_151)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_145])).

tff(c_3834,plain,(
    ! [A_355,A_356,B_357,C_358] :
      ( r2_hidden(k1_mcart_1(A_355),k2_zfmisc_1(A_356,B_357))
      | v1_xboole_0(k3_zfmisc_1(A_356,B_357,C_358))
      | ~ m1_subset_1(A_355,k3_zfmisc_1(A_356,B_357,C_358)) ) ),
    inference(resolution,[status(thm)],[c_8,c_749])).

tff(c_3931,plain,
    ( r2_hidden(k1_mcart_1('#skF_5'),k2_zfmisc_1('#skF_1','#skF_2'))
    | v1_xboole_0(k3_zfmisc_1('#skF_1','#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_46,c_3834])).

tff(c_3972,plain,(
    r2_hidden(k1_mcart_1('#skF_5'),k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_3389,c_3931])).

tff(c_18,plain,(
    ! [A_17,B_18,C_19] :
      ( r2_hidden(k1_mcart_1(A_17),B_18)
      | ~ r2_hidden(A_17,k2_zfmisc_1(B_18,C_19)) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_3977,plain,(
    r2_hidden(k1_mcart_1(k1_mcart_1('#skF_5')),'#skF_1') ),
    inference(resolution,[status(thm)],[c_3972,c_18])).

tff(c_3984,plain,(
    r2_hidden(k5_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_504,c_3977])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( m1_subset_1(A_3,B_4)
      | ~ r2_hidden(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_3998,plain,(
    m1_subset_1(k5_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_3984,c_6])).

tff(c_4002,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1062,c_3998])).

tff(c_4003,plain,(
    ~ m1_subset_1(k6_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_902])).

tff(c_341,plain,(
    ! [A_110,B_111,C_112,D_113] :
      ( k6_mcart_1(A_110,B_111,C_112,D_113) = k2_mcart_1(k1_mcart_1(D_113))
      | ~ m1_subset_1(D_113,k3_zfmisc_1(A_110,B_111,C_112))
      | k1_xboole_0 = C_112
      | k1_xboole_0 = B_111
      | k1_xboole_0 = A_110 ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_360,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_5')) = k6_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5')
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_46,c_341])).

tff(c_376,plain,(
    k2_mcart_1(k1_mcart_1('#skF_5')) = k6_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_40,c_38,c_360])).

tff(c_4630,plain,(
    ! [A_419,C_420,B_421] :
      ( r2_hidden(k2_mcart_1(A_419),C_420)
      | v1_xboole_0(k2_zfmisc_1(B_421,C_420))
      | ~ m1_subset_1(A_419,k2_zfmisc_1(B_421,C_420)) ) ),
    inference(resolution,[status(thm)],[c_8,c_108])).

tff(c_4682,plain,(
    ! [A_419,C_12,A_10,B_11] :
      ( r2_hidden(k2_mcart_1(A_419),C_12)
      | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(A_10,B_11),C_12))
      | ~ m1_subset_1(A_419,k3_zfmisc_1(A_10,B_11,C_12)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_4630])).

tff(c_6056,plain,(
    ! [A_499,C_500,A_501,B_502] :
      ( r2_hidden(k2_mcart_1(A_499),C_500)
      | v1_xboole_0(k3_zfmisc_1(A_501,B_502,C_500))
      | ~ m1_subset_1(A_499,k3_zfmisc_1(A_501,B_502,C_500)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_4682])).

tff(c_6191,plain,
    ( r2_hidden(k2_mcart_1('#skF_5'),'#skF_3')
    | v1_xboole_0(k3_zfmisc_1('#skF_1','#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_46,c_6056])).

tff(c_6195,plain,(
    v1_xboole_0(k3_zfmisc_1('#skF_1','#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_6191])).

tff(c_6201,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6195,c_96])).

tff(c_6240,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_6201,c_20])).

tff(c_6262,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_40,c_38,c_6240])).

tff(c_6264,plain,(
    ~ v1_xboole_0(k3_zfmisc_1('#skF_1','#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_6191])).

tff(c_4423,plain,(
    ! [A_406,B_407,C_408] :
      ( r2_hidden(k1_mcart_1(A_406),B_407)
      | v1_xboole_0(k2_zfmisc_1(B_407,C_408))
      | ~ m1_subset_1(A_406,k2_zfmisc_1(B_407,C_408)) ) ),
    inference(resolution,[status(thm)],[c_8,c_145])).

tff(c_4475,plain,(
    ! [A_406,A_10,B_11,C_12] :
      ( r2_hidden(k1_mcart_1(A_406),k2_zfmisc_1(A_10,B_11))
      | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(A_10,B_11),C_12))
      | ~ m1_subset_1(A_406,k3_zfmisc_1(A_10,B_11,C_12)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_4423])).

tff(c_6808,plain,(
    ! [A_538,A_539,B_540,C_541] :
      ( r2_hidden(k1_mcart_1(A_538),k2_zfmisc_1(A_539,B_540))
      | v1_xboole_0(k3_zfmisc_1(A_539,B_540,C_541))
      | ~ m1_subset_1(A_538,k3_zfmisc_1(A_539,B_540,C_541)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_4475])).

tff(c_6905,plain,
    ( r2_hidden(k1_mcart_1('#skF_5'),k2_zfmisc_1('#skF_1','#skF_2'))
    | v1_xboole_0(k3_zfmisc_1('#skF_1','#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_46,c_6808])).

tff(c_6946,plain,(
    r2_hidden(k1_mcart_1('#skF_5'),k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_6264,c_6905])).

tff(c_16,plain,(
    ! [A_17,C_19,B_18] :
      ( r2_hidden(k2_mcart_1(A_17),C_19)
      | ~ r2_hidden(A_17,k2_zfmisc_1(B_18,C_19)) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_6953,plain,(
    r2_hidden(k2_mcart_1(k1_mcart_1('#skF_5')),'#skF_2') ),
    inference(resolution,[status(thm)],[c_6946,c_16])).

tff(c_6960,plain,(
    r2_hidden(k6_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_376,c_6953])).

tff(c_6977,plain,(
    m1_subset_1(k6_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_6960,c_6])).

tff(c_6981,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4003,c_6977])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.15  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.36  % Computer   : n008.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % DateTime   : Tue Dec  1 12:22:15 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.21/0.37  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.08/2.76  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.08/2.77  
% 8.08/2.77  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.08/2.77  %$ r2_hidden > m1_subset_1 > v1_xboole_0 > k7_mcart_1 > k6_mcart_1 > k5_mcart_1 > k3_zfmisc_1 > k3_mcart_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_mcart_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 8.08/2.77  
% 8.08/2.77  %Foreground sorts:
% 8.08/2.77  
% 8.08/2.77  
% 8.08/2.77  %Background operators:
% 8.08/2.77  
% 8.08/2.77  
% 8.08/2.77  %Foreground operators:
% 8.08/2.77  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.08/2.77  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.08/2.77  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 8.08/2.77  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.08/2.77  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 8.08/2.77  tff('#skF_5', type, '#skF_5': $i).
% 8.08/2.77  tff('#skF_2', type, '#skF_2': $i).
% 8.08/2.77  tff('#skF_3', type, '#skF_3': $i).
% 8.08/2.77  tff('#skF_1', type, '#skF_1': $i).
% 8.08/2.77  tff(k7_mcart_1, type, k7_mcart_1: ($i * $i * $i * $i) > $i).
% 8.08/2.77  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 8.08/2.77  tff(k5_mcart_1, type, k5_mcart_1: ($i * $i * $i * $i) > $i).
% 8.08/2.77  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.08/2.77  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 8.08/2.77  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 8.08/2.77  tff('#skF_4', type, '#skF_4': $i).
% 8.08/2.77  tff(k6_mcart_1, type, k6_mcart_1: ($i * $i * $i * $i) > $i).
% 8.08/2.77  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.08/2.77  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 8.08/2.77  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 8.08/2.77  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.08/2.77  
% 8.08/2.79  tff(f_130, negated_conjecture, ~(![A, B, C, D, E]: (m1_subset_1(E, k3_zfmisc_1(A, B, C)) => ((![F]: (m1_subset_1(F, A) => (![G]: (m1_subset_1(G, B) => (![H]: (m1_subset_1(H, C) => ((E = k3_mcart_1(F, G, H)) => (D = H)))))))) => ((((A = k1_xboole_0) | (B = k1_xboole_0)) | (C = k1_xboole_0)) | (D = k7_mcart_1(A, B, C, E)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_mcart_1)).
% 8.08/2.79  tff(f_106, axiom, (![A, B, C]: ~(((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(![D]: (m1_subset_1(D, k3_zfmisc_1(A, B, C)) => (((k5_mcart_1(A, B, C, D) = k1_mcart_1(k1_mcart_1(D))) & (k6_mcart_1(A, B, C, D) = k2_mcart_1(k1_mcart_1(D)))) & (k7_mcart_1(A, B, C, D) = k2_mcart_1(D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_mcart_1)).
% 8.08/2.79  tff(f_52, axiom, (![A, B, C, D]: (m1_subset_1(D, k3_zfmisc_1(A, B, C)) => m1_subset_1(k7_mcart_1(A, B, C, D), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_mcart_1)).
% 8.08/2.79  tff(f_86, axiom, (![A, B, C]: ~(((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(![D]: (m1_subset_1(D, k3_zfmisc_1(A, B, C)) => (D = k3_mcart_1(k5_mcart_1(A, B, C, D), k6_mcart_1(A, B, C, D), k7_mcart_1(A, B, C, D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_mcart_1)).
% 8.08/2.79  tff(f_48, axiom, (![A, B, C]: (k3_zfmisc_1(A, B, C) = k2_zfmisc_1(k2_zfmisc_1(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 8.08/2.79  tff(f_44, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 8.08/2.79  tff(f_58, axiom, (![A, B, C]: (r2_hidden(A, k2_zfmisc_1(B, C)) => (r2_hidden(k1_mcart_1(A), B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_mcart_1)).
% 8.08/2.79  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 8.08/2.79  tff(f_34, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_boole)).
% 8.08/2.79  tff(f_70, axiom, (![A, B, C]: (((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) <=> ~(k3_zfmisc_1(A, B, C) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_mcart_1)).
% 8.08/2.79  tff(f_38, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 8.08/2.79  tff(c_42, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_130])).
% 8.08/2.79  tff(c_40, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_130])).
% 8.08/2.79  tff(c_38, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_130])).
% 8.08/2.79  tff(c_46, plain, (m1_subset_1('#skF_5', k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_130])).
% 8.08/2.79  tff(c_292, plain, (![A_106, B_107, C_108, D_109]: (k7_mcart_1(A_106, B_107, C_108, D_109)=k2_mcart_1(D_109) | ~m1_subset_1(D_109, k3_zfmisc_1(A_106, B_107, C_108)) | k1_xboole_0=C_108 | k1_xboole_0=B_107 | k1_xboole_0=A_106)), inference(cnfTransformation, [status(thm)], [f_106])).
% 8.08/2.79  tff(c_311, plain, (k7_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5')=k2_mcart_1('#skF_5') | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_46, c_292])).
% 8.08/2.79  tff(c_327, plain, (k7_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5')=k2_mcart_1('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_42, c_40, c_38, c_311])).
% 8.08/2.79  tff(c_36, plain, (k7_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_130])).
% 8.08/2.79  tff(c_331, plain, (k2_mcart_1('#skF_5')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_327, c_36])).
% 8.08/2.79  tff(c_14, plain, (![A_13, B_14, C_15, D_16]: (m1_subset_1(k7_mcart_1(A_13, B_14, C_15, D_16), C_15) | ~m1_subset_1(D_16, k3_zfmisc_1(A_13, B_14, C_15)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 8.08/2.79  tff(c_335, plain, (m1_subset_1(k2_mcart_1('#skF_5'), '#skF_3') | ~m1_subset_1('#skF_5', k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_327, c_14])).
% 8.08/2.79  tff(c_339, plain, (m1_subset_1(k2_mcart_1('#skF_5'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_335])).
% 8.08/2.79  tff(c_642, plain, (![A_136, B_137, C_138, D_139]: (k3_mcart_1(k5_mcart_1(A_136, B_137, C_138, D_139), k6_mcart_1(A_136, B_137, C_138, D_139), k7_mcart_1(A_136, B_137, C_138, D_139))=D_139 | ~m1_subset_1(D_139, k3_zfmisc_1(A_136, B_137, C_138)) | k1_xboole_0=C_138 | k1_xboole_0=B_137 | k1_xboole_0=A_136)), inference(cnfTransformation, [status(thm)], [f_86])).
% 8.08/2.79  tff(c_44, plain, (![H_46, F_40, G_44]: (H_46='#skF_4' | k3_mcart_1(F_40, G_44, H_46)!='#skF_5' | ~m1_subset_1(H_46, '#skF_3') | ~m1_subset_1(G_44, '#skF_2') | ~m1_subset_1(F_40, '#skF_1'))), inference(cnfTransformation, [status(thm)], [f_130])).
% 8.08/2.79  tff(c_891, plain, (![A_159, B_160, C_161, D_162]: (k7_mcart_1(A_159, B_160, C_161, D_162)='#skF_4' | D_162!='#skF_5' | ~m1_subset_1(k7_mcart_1(A_159, B_160, C_161, D_162), '#skF_3') | ~m1_subset_1(k6_mcart_1(A_159, B_160, C_161, D_162), '#skF_2') | ~m1_subset_1(k5_mcart_1(A_159, B_160, C_161, D_162), '#skF_1') | ~m1_subset_1(D_162, k3_zfmisc_1(A_159, B_160, C_161)) | k1_xboole_0=C_161 | k1_xboole_0=B_160 | k1_xboole_0=A_159)), inference(superposition, [status(thm), theory('equality')], [c_642, c_44])).
% 8.08/2.79  tff(c_894, plain, (k7_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5')='#skF_4' | ~m1_subset_1(k2_mcart_1('#skF_5'), '#skF_3') | ~m1_subset_1(k6_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_2') | ~m1_subset_1(k5_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_1') | ~m1_subset_1('#skF_5', k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')) | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_327, c_891])).
% 8.08/2.79  tff(c_901, plain, (k2_mcart_1('#skF_5')='#skF_4' | ~m1_subset_1(k6_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_2') | ~m1_subset_1(k5_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_1') | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_46, c_339, c_327, c_894])).
% 8.08/2.79  tff(c_902, plain, (~m1_subset_1(k6_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_2') | ~m1_subset_1(k5_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_42, c_40, c_38, c_331, c_901])).
% 8.08/2.79  tff(c_1062, plain, (~m1_subset_1(k5_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_1')), inference(splitLeft, [status(thm)], [c_902])).
% 8.08/2.79  tff(c_459, plain, (![A_120, B_121, C_122, D_123]: (k5_mcart_1(A_120, B_121, C_122, D_123)=k1_mcart_1(k1_mcart_1(D_123)) | ~m1_subset_1(D_123, k3_zfmisc_1(A_120, B_121, C_122)) | k1_xboole_0=C_122 | k1_xboole_0=B_121 | k1_xboole_0=A_120)), inference(cnfTransformation, [status(thm)], [f_106])).
% 8.08/2.79  tff(c_486, plain, (k1_mcart_1(k1_mcart_1('#skF_5'))=k5_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5') | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_46, c_459])).
% 8.08/2.79  tff(c_504, plain, (k1_mcart_1(k1_mcart_1('#skF_5'))=k5_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_42, c_40, c_38, c_486])).
% 8.08/2.79  tff(c_12, plain, (![A_10, B_11, C_12]: (k2_zfmisc_1(k2_zfmisc_1(A_10, B_11), C_12)=k3_zfmisc_1(A_10, B_11, C_12))), inference(cnfTransformation, [status(thm)], [f_48])).
% 8.08/2.79  tff(c_8, plain, (![A_5, B_6]: (r2_hidden(A_5, B_6) | v1_xboole_0(B_6) | ~m1_subset_1(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_44])).
% 8.08/2.79  tff(c_108, plain, (![A_60, C_61, B_62]: (r2_hidden(k2_mcart_1(A_60), C_61) | ~r2_hidden(A_60, k2_zfmisc_1(B_62, C_61)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 8.08/2.79  tff(c_1509, plain, (![A_227, C_228, B_229]: (r2_hidden(k2_mcart_1(A_227), C_228) | v1_xboole_0(k2_zfmisc_1(B_229, C_228)) | ~m1_subset_1(A_227, k2_zfmisc_1(B_229, C_228)))), inference(resolution, [status(thm)], [c_8, c_108])).
% 8.08/2.79  tff(c_1561, plain, (![A_227, C_12, A_10, B_11]: (r2_hidden(k2_mcart_1(A_227), C_12) | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(A_10, B_11), C_12)) | ~m1_subset_1(A_227, k3_zfmisc_1(A_10, B_11, C_12)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_1509])).
% 8.08/2.79  tff(c_3181, plain, (![A_322, C_323, A_324, B_325]: (r2_hidden(k2_mcart_1(A_322), C_323) | v1_xboole_0(k3_zfmisc_1(A_324, B_325, C_323)) | ~m1_subset_1(A_322, k3_zfmisc_1(A_324, B_325, C_323)))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_1561])).
% 8.08/2.79  tff(c_3316, plain, (r2_hidden(k2_mcart_1('#skF_5'), '#skF_3') | v1_xboole_0(k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_46, c_3181])).
% 8.08/2.79  tff(c_3320, plain, (v1_xboole_0(k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_3316])).
% 8.08/2.79  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 8.08/2.79  tff(c_93, plain, (![B_55, A_56]: (~v1_xboole_0(B_55) | B_55=A_56 | ~v1_xboole_0(A_56))), inference(cnfTransformation, [status(thm)], [f_34])).
% 8.08/2.79  tff(c_96, plain, (![A_56]: (k1_xboole_0=A_56 | ~v1_xboole_0(A_56))), inference(resolution, [status(thm)], [c_2, c_93])).
% 8.08/2.79  tff(c_3326, plain, (k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_3320, c_96])).
% 8.08/2.79  tff(c_20, plain, (![A_20, B_21, C_22]: (k3_zfmisc_1(A_20, B_21, C_22)!=k1_xboole_0 | k1_xboole_0=C_22 | k1_xboole_0=B_21 | k1_xboole_0=A_20)), inference(cnfTransformation, [status(thm)], [f_70])).
% 8.08/2.79  tff(c_3365, plain, (k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_3326, c_20])).
% 8.08/2.79  tff(c_3387, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_40, c_38, c_3365])).
% 8.08/2.79  tff(c_3389, plain, (~v1_xboole_0(k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_3316])).
% 8.08/2.79  tff(c_145, plain, (![A_69, B_70, C_71]: (r2_hidden(k1_mcart_1(A_69), B_70) | ~r2_hidden(A_69, k2_zfmisc_1(B_70, C_71)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 8.08/2.79  tff(c_749, plain, (![A_148, A_149, B_150, C_151]: (r2_hidden(k1_mcart_1(A_148), k2_zfmisc_1(A_149, B_150)) | ~r2_hidden(A_148, k3_zfmisc_1(A_149, B_150, C_151)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_145])).
% 8.08/2.79  tff(c_3834, plain, (![A_355, A_356, B_357, C_358]: (r2_hidden(k1_mcart_1(A_355), k2_zfmisc_1(A_356, B_357)) | v1_xboole_0(k3_zfmisc_1(A_356, B_357, C_358)) | ~m1_subset_1(A_355, k3_zfmisc_1(A_356, B_357, C_358)))), inference(resolution, [status(thm)], [c_8, c_749])).
% 8.08/2.79  tff(c_3931, plain, (r2_hidden(k1_mcart_1('#skF_5'), k2_zfmisc_1('#skF_1', '#skF_2')) | v1_xboole_0(k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_46, c_3834])).
% 8.08/2.79  tff(c_3972, plain, (r2_hidden(k1_mcart_1('#skF_5'), k2_zfmisc_1('#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_3389, c_3931])).
% 8.08/2.79  tff(c_18, plain, (![A_17, B_18, C_19]: (r2_hidden(k1_mcart_1(A_17), B_18) | ~r2_hidden(A_17, k2_zfmisc_1(B_18, C_19)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 8.08/2.79  tff(c_3977, plain, (r2_hidden(k1_mcart_1(k1_mcart_1('#skF_5')), '#skF_1')), inference(resolution, [status(thm)], [c_3972, c_18])).
% 8.08/2.79  tff(c_3984, plain, (r2_hidden(k5_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_504, c_3977])).
% 8.08/2.79  tff(c_6, plain, (![A_3, B_4]: (m1_subset_1(A_3, B_4) | ~r2_hidden(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_38])).
% 8.08/2.79  tff(c_3998, plain, (m1_subset_1(k5_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_1')), inference(resolution, [status(thm)], [c_3984, c_6])).
% 8.08/2.79  tff(c_4002, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1062, c_3998])).
% 8.08/2.79  tff(c_4003, plain, (~m1_subset_1(k6_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_2')), inference(splitRight, [status(thm)], [c_902])).
% 8.08/2.79  tff(c_341, plain, (![A_110, B_111, C_112, D_113]: (k6_mcart_1(A_110, B_111, C_112, D_113)=k2_mcart_1(k1_mcart_1(D_113)) | ~m1_subset_1(D_113, k3_zfmisc_1(A_110, B_111, C_112)) | k1_xboole_0=C_112 | k1_xboole_0=B_111 | k1_xboole_0=A_110)), inference(cnfTransformation, [status(thm)], [f_106])).
% 8.08/2.79  tff(c_360, plain, (k2_mcart_1(k1_mcart_1('#skF_5'))=k6_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5') | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_46, c_341])).
% 8.08/2.79  tff(c_376, plain, (k2_mcart_1(k1_mcart_1('#skF_5'))=k6_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_42, c_40, c_38, c_360])).
% 8.08/2.79  tff(c_4630, plain, (![A_419, C_420, B_421]: (r2_hidden(k2_mcart_1(A_419), C_420) | v1_xboole_0(k2_zfmisc_1(B_421, C_420)) | ~m1_subset_1(A_419, k2_zfmisc_1(B_421, C_420)))), inference(resolution, [status(thm)], [c_8, c_108])).
% 8.08/2.79  tff(c_4682, plain, (![A_419, C_12, A_10, B_11]: (r2_hidden(k2_mcart_1(A_419), C_12) | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(A_10, B_11), C_12)) | ~m1_subset_1(A_419, k3_zfmisc_1(A_10, B_11, C_12)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_4630])).
% 8.08/2.79  tff(c_6056, plain, (![A_499, C_500, A_501, B_502]: (r2_hidden(k2_mcart_1(A_499), C_500) | v1_xboole_0(k3_zfmisc_1(A_501, B_502, C_500)) | ~m1_subset_1(A_499, k3_zfmisc_1(A_501, B_502, C_500)))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_4682])).
% 8.08/2.79  tff(c_6191, plain, (r2_hidden(k2_mcart_1('#skF_5'), '#skF_3') | v1_xboole_0(k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_46, c_6056])).
% 8.08/2.79  tff(c_6195, plain, (v1_xboole_0(k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_6191])).
% 8.08/2.79  tff(c_6201, plain, (k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_6195, c_96])).
% 8.08/2.79  tff(c_6240, plain, (k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_6201, c_20])).
% 8.08/2.79  tff(c_6262, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_40, c_38, c_6240])).
% 8.08/2.79  tff(c_6264, plain, (~v1_xboole_0(k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_6191])).
% 8.08/2.79  tff(c_4423, plain, (![A_406, B_407, C_408]: (r2_hidden(k1_mcart_1(A_406), B_407) | v1_xboole_0(k2_zfmisc_1(B_407, C_408)) | ~m1_subset_1(A_406, k2_zfmisc_1(B_407, C_408)))), inference(resolution, [status(thm)], [c_8, c_145])).
% 8.08/2.79  tff(c_4475, plain, (![A_406, A_10, B_11, C_12]: (r2_hidden(k1_mcart_1(A_406), k2_zfmisc_1(A_10, B_11)) | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(A_10, B_11), C_12)) | ~m1_subset_1(A_406, k3_zfmisc_1(A_10, B_11, C_12)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_4423])).
% 8.08/2.79  tff(c_6808, plain, (![A_538, A_539, B_540, C_541]: (r2_hidden(k1_mcart_1(A_538), k2_zfmisc_1(A_539, B_540)) | v1_xboole_0(k3_zfmisc_1(A_539, B_540, C_541)) | ~m1_subset_1(A_538, k3_zfmisc_1(A_539, B_540, C_541)))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_4475])).
% 8.08/2.79  tff(c_6905, plain, (r2_hidden(k1_mcart_1('#skF_5'), k2_zfmisc_1('#skF_1', '#skF_2')) | v1_xboole_0(k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_46, c_6808])).
% 8.08/2.79  tff(c_6946, plain, (r2_hidden(k1_mcart_1('#skF_5'), k2_zfmisc_1('#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_6264, c_6905])).
% 8.08/2.79  tff(c_16, plain, (![A_17, C_19, B_18]: (r2_hidden(k2_mcart_1(A_17), C_19) | ~r2_hidden(A_17, k2_zfmisc_1(B_18, C_19)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 8.08/2.79  tff(c_6953, plain, (r2_hidden(k2_mcart_1(k1_mcart_1('#skF_5')), '#skF_2')), inference(resolution, [status(thm)], [c_6946, c_16])).
% 8.08/2.79  tff(c_6960, plain, (r2_hidden(k6_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_376, c_6953])).
% 8.08/2.79  tff(c_6977, plain, (m1_subset_1(k6_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_2')), inference(resolution, [status(thm)], [c_6960, c_6])).
% 8.08/2.79  tff(c_6981, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4003, c_6977])).
% 8.08/2.79  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.08/2.79  
% 8.08/2.79  Inference rules
% 8.08/2.79  ----------------------
% 8.08/2.79  #Ref     : 0
% 8.08/2.79  #Sup     : 1799
% 8.08/2.79  #Fact    : 0
% 8.08/2.79  #Define  : 0
% 8.08/2.79  #Split   : 6
% 8.08/2.79  #Chain   : 0
% 8.08/2.79  #Close   : 0
% 8.08/2.79  
% 8.08/2.79  Ordering : KBO
% 8.08/2.79  
% 8.08/2.79  Simplification rules
% 8.08/2.79  ----------------------
% 8.08/2.79  #Subsume      : 515
% 8.08/2.79  #Demod        : 380
% 8.08/2.79  #Tautology    : 211
% 8.08/2.79  #SimpNegUnit  : 31
% 8.08/2.79  #BackRed      : 5
% 8.08/2.79  
% 8.08/2.79  #Partial instantiations: 0
% 8.08/2.79  #Strategies tried      : 1
% 8.08/2.79  
% 8.08/2.79  Timing (in seconds)
% 8.08/2.79  ----------------------
% 8.08/2.79  Preprocessing        : 0.35
% 8.08/2.79  Parsing              : 0.19
% 8.08/2.79  CNF conversion       : 0.02
% 8.08/2.79  Main loop            : 1.59
% 8.08/2.80  Inferencing          : 0.49
% 8.08/2.80  Reduction            : 0.39
% 8.08/2.80  Demodulation         : 0.26
% 8.08/2.80  BG Simplification    : 0.07
% 8.08/2.80  Subsumption          : 0.51
% 8.08/2.80  Abstraction          : 0.09
% 8.08/2.80  MUC search           : 0.00
% 8.08/2.80  Cooper               : 0.00
% 8.08/2.80  Total                : 1.98
% 8.08/2.80  Index Insertion      : 0.00
% 8.08/2.80  Index Deletion       : 0.00
% 8.08/2.80  Index Matching       : 0.00
% 8.08/2.80  BG Taut test         : 0.00
%------------------------------------------------------------------------------
