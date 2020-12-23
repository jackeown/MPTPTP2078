%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:49:17 EST 2020

% Result     : Theorem 3.44s
% Output     : CNFRefutation 3.44s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 158 expanded)
%              Number of leaves         :   32 (  67 expanded)
%              Depth                    :   17
%              Number of atoms          :   53 ( 168 expanded)
%              Number of equality atoms :   40 ( 138 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_3 > #skF_5 > #skF_2 > #skF_6 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_59,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_57,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_61,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_63,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_65,axiom,(
    ! [A,B,C,D,E,F] : k5_enumset1(A,A,B,C,D,E,F) = k4_enumset1(A,B,C,D,E,F) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

tff(f_67,axiom,(
    ! [A,B,C,D,E,F,G] : k6_enumset1(A,A,B,C,D,E,F,G) = k5_enumset1(A,B,C,D,E,F,G) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

tff(f_53,axiom,(
    ! [A,B,C,D,E,F,G,H] : k6_enumset1(A,B,C,D,E,F,G,H) = k2_xboole_0(k5_enumset1(A,B,C,D,E,F,G),k1_tarski(H)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t68_enumset1)).

tff(f_72,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(k2_tarski(A,B),k1_tarski(C))
       => A = C ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_44,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(c_46,plain,(
    ! [A_26,B_27,C_28] : k2_enumset1(A_26,A_26,B_27,C_28) = k1_enumset1(A_26,B_27,C_28) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_44,plain,(
    ! [A_24,B_25] : k1_enumset1(A_24,A_24,B_25) = k2_tarski(A_24,B_25) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_48,plain,(
    ! [A_29,B_30,C_31,D_32] : k3_enumset1(A_29,A_29,B_30,C_31,D_32) = k2_enumset1(A_29,B_30,C_31,D_32) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_50,plain,(
    ! [D_36,E_37,A_33,B_34,C_35] : k4_enumset1(A_33,A_33,B_34,C_35,D_36,E_37) = k3_enumset1(A_33,B_34,C_35,D_36,E_37) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_52,plain,(
    ! [D_41,B_39,A_38,F_43,E_42,C_40] : k5_enumset1(A_38,A_38,B_39,C_40,D_41,E_42,F_43) = k4_enumset1(A_38,B_39,C_40,D_41,E_42,F_43) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_54,plain,(
    ! [C_46,E_48,F_49,G_50,A_44,B_45,D_47] : k6_enumset1(A_44,A_44,B_45,C_46,D_47,E_48,F_49,G_50) = k5_enumset1(A_44,B_45,C_46,D_47,E_48,F_49,G_50) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_1716,plain,(
    ! [A_2847,B_2844,D_2842,F_2845,C_2840,E_2846,H_2841,G_2843] : k2_xboole_0(k5_enumset1(A_2847,B_2844,C_2840,D_2842,E_2846,F_2845,G_2843),k1_tarski(H_2841)) = k6_enumset1(A_2847,B_2844,C_2840,D_2842,E_2846,F_2845,G_2843,H_2841) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1725,plain,(
    ! [D_41,B_39,A_38,F_43,H_2841,E_42,C_40] : k6_enumset1(A_38,A_38,B_39,C_40,D_41,E_42,F_43,H_2841) = k2_xboole_0(k4_enumset1(A_38,B_39,C_40,D_41,E_42,F_43),k1_tarski(H_2841)) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_1716])).

tff(c_1829,plain,(
    ! [H_2955,A_2950,C_2954,F_2953,D_2956,E_2952,B_2951] : k2_xboole_0(k4_enumset1(A_2950,B_2951,C_2954,D_2956,E_2952,F_2953),k1_tarski(H_2955)) = k5_enumset1(A_2950,B_2951,C_2954,D_2956,E_2952,F_2953,H_2955) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_1725])).

tff(c_1838,plain,(
    ! [H_2955,D_36,E_37,A_33,B_34,C_35] : k5_enumset1(A_33,A_33,B_34,C_35,D_36,E_37,H_2955) = k2_xboole_0(k3_enumset1(A_33,B_34,C_35,D_36,E_37),k1_tarski(H_2955)) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_1829])).

tff(c_1886,plain,(
    ! [E_3008,D_3010,B_3012,A_3007,C_3009,H_3011] : k2_xboole_0(k3_enumset1(A_3007,B_3012,C_3009,D_3010,E_3008),k1_tarski(H_3011)) = k4_enumset1(A_3007,B_3012,C_3009,D_3010,E_3008,H_3011) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_1838])).

tff(c_1939,plain,(
    ! [A_29,H_3011,D_32,C_31,B_30] : k4_enumset1(A_29,A_29,B_30,C_31,D_32,H_3011) = k2_xboole_0(k2_enumset1(A_29,B_30,C_31,D_32),k1_tarski(H_3011)) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_1886])).

tff(c_1943,plain,(
    ! [D_3063,A_3066,H_3065,B_3064,C_3067] : k2_xboole_0(k2_enumset1(A_3066,B_3064,C_3067,D_3063),k1_tarski(H_3065)) = k3_enumset1(A_3066,B_3064,C_3067,D_3063,H_3065) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_1939])).

tff(c_1996,plain,(
    ! [A_26,B_27,C_28,H_3065] : k3_enumset1(A_26,A_26,B_27,C_28,H_3065) = k2_xboole_0(k1_enumset1(A_26,B_27,C_28),k1_tarski(H_3065)) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_1943])).

tff(c_2002,plain,(
    ! [A_3172,B_3173,C_3174,H_3175] : k2_xboole_0(k1_enumset1(A_3172,B_3173,C_3174),k1_tarski(H_3175)) = k2_enumset1(A_3172,B_3173,C_3174,H_3175) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_1996])).

tff(c_2055,plain,(
    ! [A_24,B_25,H_3175] : k2_xboole_0(k2_tarski(A_24,B_25),k1_tarski(H_3175)) = k2_enumset1(A_24,A_24,B_25,H_3175) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_2002])).

tff(c_2059,plain,(
    ! [A_3226,B_3227,H_3228] : k2_xboole_0(k2_tarski(A_3226,B_3227),k1_tarski(H_3228)) = k1_enumset1(A_3226,B_3227,H_3228) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_2055])).

tff(c_58,plain,(
    r1_tarski(k2_tarski('#skF_5','#skF_6'),k1_tarski('#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_78,plain,(
    ! [A_64,B_65] :
      ( k2_xboole_0(A_64,B_65) = B_65
      | ~ r1_tarski(A_64,B_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_82,plain,(
    k2_xboole_0(k2_tarski('#skF_5','#skF_6'),k1_tarski('#skF_7')) = k1_tarski('#skF_7') ),
    inference(resolution,[status(thm)],[c_58,c_78])).

tff(c_2065,plain,(
    k1_enumset1('#skF_5','#skF_6','#skF_7') = k1_tarski('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_2059,c_82])).

tff(c_8,plain,(
    ! [E_9,A_3,C_5] : r2_hidden(E_9,k1_enumset1(A_3,E_9,C_5)) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_2149,plain,(
    r2_hidden('#skF_6',k1_tarski('#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2065,c_8])).

tff(c_28,plain,(
    ! [C_14,A_10] :
      ( C_14 = A_10
      | ~ r2_hidden(C_14,k1_tarski(A_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_2228,plain,(
    '#skF_7' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_2149,c_28])).

tff(c_56,plain,(
    '#skF_7' != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_2238,plain,(
    '#skF_5' != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2228,c_56])).

tff(c_10,plain,(
    ! [E_9,B_4,C_5] : r2_hidden(E_9,k1_enumset1(E_9,B_4,C_5)) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_2155,plain,(
    r2_hidden('#skF_5',k1_tarski('#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2065,c_10])).

tff(c_2244,plain,(
    r2_hidden('#skF_5',k1_tarski('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2228,c_2155])).

tff(c_2252,plain,(
    '#skF_5' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_2244,c_28])).

tff(c_2292,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2238,c_2252])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n006.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 12:33:22 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.44/1.60  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.44/1.61  
% 3.44/1.61  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.44/1.61  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_3 > #skF_5 > #skF_2 > #skF_6 > #skF_1 > #skF_4
% 3.44/1.61  
% 3.44/1.61  %Foreground sorts:
% 3.44/1.61  
% 3.44/1.61  
% 3.44/1.61  %Background operators:
% 3.44/1.61  
% 3.44/1.61  
% 3.44/1.61  %Foreground operators:
% 3.44/1.61  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.44/1.61  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.44/1.61  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.44/1.61  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.44/1.61  tff('#skF_7', type, '#skF_7': $i).
% 3.44/1.61  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.44/1.61  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.44/1.61  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.44/1.61  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.44/1.61  tff('#skF_5', type, '#skF_5': $i).
% 3.44/1.61  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 3.44/1.61  tff('#skF_6', type, '#skF_6': $i).
% 3.44/1.61  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.44/1.61  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.44/1.61  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.44/1.61  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.44/1.61  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.44/1.61  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.44/1.61  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.44/1.61  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 3.44/1.61  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 3.44/1.61  
% 3.44/1.62  tff(f_59, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 3.44/1.62  tff(f_57, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 3.44/1.62  tff(f_61, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 3.44/1.62  tff(f_63, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 3.44/1.62  tff(f_65, axiom, (![A, B, C, D, E, F]: (k5_enumset1(A, A, B, C, D, E, F) = k4_enumset1(A, B, C, D, E, F))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_enumset1)).
% 3.44/1.62  tff(f_67, axiom, (![A, B, C, D, E, F, G]: (k6_enumset1(A, A, B, C, D, E, F, G) = k5_enumset1(A, B, C, D, E, F, G))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t75_enumset1)).
% 3.44/1.62  tff(f_53, axiom, (![A, B, C, D, E, F, G, H]: (k6_enumset1(A, B, C, D, E, F, G, H) = k2_xboole_0(k5_enumset1(A, B, C, D, E, F, G), k1_tarski(H)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t68_enumset1)).
% 3.44/1.62  tff(f_72, negated_conjecture, ~(![A, B, C]: (r1_tarski(k2_tarski(A, B), k1_tarski(C)) => (A = C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_zfmisc_1)).
% 3.44/1.62  tff(f_29, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 3.44/1.62  tff(f_44, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 3.44/1.62  tff(f_51, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 3.44/1.62  tff(c_46, plain, (![A_26, B_27, C_28]: (k2_enumset1(A_26, A_26, B_27, C_28)=k1_enumset1(A_26, B_27, C_28))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.44/1.62  tff(c_44, plain, (![A_24, B_25]: (k1_enumset1(A_24, A_24, B_25)=k2_tarski(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.44/1.62  tff(c_48, plain, (![A_29, B_30, C_31, D_32]: (k3_enumset1(A_29, A_29, B_30, C_31, D_32)=k2_enumset1(A_29, B_30, C_31, D_32))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.44/1.62  tff(c_50, plain, (![D_36, E_37, A_33, B_34, C_35]: (k4_enumset1(A_33, A_33, B_34, C_35, D_36, E_37)=k3_enumset1(A_33, B_34, C_35, D_36, E_37))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.44/1.62  tff(c_52, plain, (![D_41, B_39, A_38, F_43, E_42, C_40]: (k5_enumset1(A_38, A_38, B_39, C_40, D_41, E_42, F_43)=k4_enumset1(A_38, B_39, C_40, D_41, E_42, F_43))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.44/1.62  tff(c_54, plain, (![C_46, E_48, F_49, G_50, A_44, B_45, D_47]: (k6_enumset1(A_44, A_44, B_45, C_46, D_47, E_48, F_49, G_50)=k5_enumset1(A_44, B_45, C_46, D_47, E_48, F_49, G_50))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.44/1.62  tff(c_1716, plain, (![A_2847, B_2844, D_2842, F_2845, C_2840, E_2846, H_2841, G_2843]: (k2_xboole_0(k5_enumset1(A_2847, B_2844, C_2840, D_2842, E_2846, F_2845, G_2843), k1_tarski(H_2841))=k6_enumset1(A_2847, B_2844, C_2840, D_2842, E_2846, F_2845, G_2843, H_2841))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.44/1.62  tff(c_1725, plain, (![D_41, B_39, A_38, F_43, H_2841, E_42, C_40]: (k6_enumset1(A_38, A_38, B_39, C_40, D_41, E_42, F_43, H_2841)=k2_xboole_0(k4_enumset1(A_38, B_39, C_40, D_41, E_42, F_43), k1_tarski(H_2841)))), inference(superposition, [status(thm), theory('equality')], [c_52, c_1716])).
% 3.44/1.62  tff(c_1829, plain, (![H_2955, A_2950, C_2954, F_2953, D_2956, E_2952, B_2951]: (k2_xboole_0(k4_enumset1(A_2950, B_2951, C_2954, D_2956, E_2952, F_2953), k1_tarski(H_2955))=k5_enumset1(A_2950, B_2951, C_2954, D_2956, E_2952, F_2953, H_2955))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_1725])).
% 3.44/1.62  tff(c_1838, plain, (![H_2955, D_36, E_37, A_33, B_34, C_35]: (k5_enumset1(A_33, A_33, B_34, C_35, D_36, E_37, H_2955)=k2_xboole_0(k3_enumset1(A_33, B_34, C_35, D_36, E_37), k1_tarski(H_2955)))), inference(superposition, [status(thm), theory('equality')], [c_50, c_1829])).
% 3.44/1.62  tff(c_1886, plain, (![E_3008, D_3010, B_3012, A_3007, C_3009, H_3011]: (k2_xboole_0(k3_enumset1(A_3007, B_3012, C_3009, D_3010, E_3008), k1_tarski(H_3011))=k4_enumset1(A_3007, B_3012, C_3009, D_3010, E_3008, H_3011))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_1838])).
% 3.44/1.62  tff(c_1939, plain, (![A_29, H_3011, D_32, C_31, B_30]: (k4_enumset1(A_29, A_29, B_30, C_31, D_32, H_3011)=k2_xboole_0(k2_enumset1(A_29, B_30, C_31, D_32), k1_tarski(H_3011)))), inference(superposition, [status(thm), theory('equality')], [c_48, c_1886])).
% 3.44/1.62  tff(c_1943, plain, (![D_3063, A_3066, H_3065, B_3064, C_3067]: (k2_xboole_0(k2_enumset1(A_3066, B_3064, C_3067, D_3063), k1_tarski(H_3065))=k3_enumset1(A_3066, B_3064, C_3067, D_3063, H_3065))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_1939])).
% 3.44/1.62  tff(c_1996, plain, (![A_26, B_27, C_28, H_3065]: (k3_enumset1(A_26, A_26, B_27, C_28, H_3065)=k2_xboole_0(k1_enumset1(A_26, B_27, C_28), k1_tarski(H_3065)))), inference(superposition, [status(thm), theory('equality')], [c_46, c_1943])).
% 3.44/1.62  tff(c_2002, plain, (![A_3172, B_3173, C_3174, H_3175]: (k2_xboole_0(k1_enumset1(A_3172, B_3173, C_3174), k1_tarski(H_3175))=k2_enumset1(A_3172, B_3173, C_3174, H_3175))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_1996])).
% 3.44/1.62  tff(c_2055, plain, (![A_24, B_25, H_3175]: (k2_xboole_0(k2_tarski(A_24, B_25), k1_tarski(H_3175))=k2_enumset1(A_24, A_24, B_25, H_3175))), inference(superposition, [status(thm), theory('equality')], [c_44, c_2002])).
% 3.44/1.62  tff(c_2059, plain, (![A_3226, B_3227, H_3228]: (k2_xboole_0(k2_tarski(A_3226, B_3227), k1_tarski(H_3228))=k1_enumset1(A_3226, B_3227, H_3228))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_2055])).
% 3.44/1.62  tff(c_58, plain, (r1_tarski(k2_tarski('#skF_5', '#skF_6'), k1_tarski('#skF_7'))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.44/1.62  tff(c_78, plain, (![A_64, B_65]: (k2_xboole_0(A_64, B_65)=B_65 | ~r1_tarski(A_64, B_65))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.44/1.62  tff(c_82, plain, (k2_xboole_0(k2_tarski('#skF_5', '#skF_6'), k1_tarski('#skF_7'))=k1_tarski('#skF_7')), inference(resolution, [status(thm)], [c_58, c_78])).
% 3.44/1.62  tff(c_2065, plain, (k1_enumset1('#skF_5', '#skF_6', '#skF_7')=k1_tarski('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_2059, c_82])).
% 3.44/1.62  tff(c_8, plain, (![E_9, A_3, C_5]: (r2_hidden(E_9, k1_enumset1(A_3, E_9, C_5)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.44/1.62  tff(c_2149, plain, (r2_hidden('#skF_6', k1_tarski('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_2065, c_8])).
% 3.44/1.62  tff(c_28, plain, (![C_14, A_10]: (C_14=A_10 | ~r2_hidden(C_14, k1_tarski(A_10)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.44/1.62  tff(c_2228, plain, ('#skF_7'='#skF_6'), inference(resolution, [status(thm)], [c_2149, c_28])).
% 3.44/1.62  tff(c_56, plain, ('#skF_7'!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.44/1.62  tff(c_2238, plain, ('#skF_5'!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_2228, c_56])).
% 3.44/1.62  tff(c_10, plain, (![E_9, B_4, C_5]: (r2_hidden(E_9, k1_enumset1(E_9, B_4, C_5)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.44/1.62  tff(c_2155, plain, (r2_hidden('#skF_5', k1_tarski('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_2065, c_10])).
% 3.44/1.62  tff(c_2244, plain, (r2_hidden('#skF_5', k1_tarski('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_2228, c_2155])).
% 3.44/1.62  tff(c_2252, plain, ('#skF_5'='#skF_6'), inference(resolution, [status(thm)], [c_2244, c_28])).
% 3.44/1.62  tff(c_2292, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2238, c_2252])).
% 3.44/1.62  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.44/1.62  
% 3.44/1.62  Inference rules
% 3.44/1.62  ----------------------
% 3.44/1.62  #Ref     : 0
% 3.44/1.62  #Sup     : 321
% 3.44/1.62  #Fact    : 6
% 3.44/1.62  #Define  : 0
% 3.44/1.62  #Split   : 3
% 3.44/1.62  #Chain   : 0
% 3.44/1.62  #Close   : 0
% 3.44/1.62  
% 3.44/1.62  Ordering : KBO
% 3.44/1.62  
% 3.44/1.62  Simplification rules
% 3.44/1.62  ----------------------
% 3.44/1.62  #Subsume      : 26
% 3.44/1.62  #Demod        : 49
% 3.44/1.62  #Tautology    : 172
% 3.44/1.62  #SimpNegUnit  : 3
% 3.44/1.62  #BackRed      : 10
% 3.44/1.62  
% 3.44/1.62  #Partial instantiations: 1040
% 3.44/1.62  #Strategies tried      : 1
% 3.44/1.62  
% 3.44/1.62  Timing (in seconds)
% 3.44/1.62  ----------------------
% 3.44/1.63  Preprocessing        : 0.31
% 3.44/1.63  Parsing              : 0.16
% 3.44/1.63  CNF conversion       : 0.02
% 3.44/1.63  Main loop            : 0.56
% 3.44/1.63  Inferencing          : 0.28
% 3.44/1.63  Reduction            : 0.12
% 3.44/1.63  Demodulation         : 0.08
% 3.44/1.63  BG Simplification    : 0.03
% 3.44/1.63  Subsumption          : 0.10
% 3.44/1.63  Abstraction          : 0.03
% 3.44/1.63  MUC search           : 0.00
% 3.44/1.63  Cooper               : 0.00
% 3.44/1.63  Total                : 0.90
% 3.44/1.63  Index Insertion      : 0.00
% 3.44/1.63  Index Deletion       : 0.00
% 3.44/1.63  Index Matching       : 0.00
% 3.44/1.63  BG Taut test         : 0.00
%------------------------------------------------------------------------------
