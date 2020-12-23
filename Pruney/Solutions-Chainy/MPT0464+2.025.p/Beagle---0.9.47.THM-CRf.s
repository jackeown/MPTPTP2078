%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:46 EST 2020

% Result     : Theorem 3.12s
% Output     : CNFRefutation 3.17s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 120 expanded)
%              Number of leaves         :   38 (  56 expanded)
%              Depth                    :    9
%              Number of atoms          :  106 ( 210 expanded)
%              Number of equality atoms :   23 (  23 expanded)
%              Maximal formula depth    :   22 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_setfam_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_35,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_39,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_41,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_43,axiom,(
    ! [A,B,C,D,E,F] : k5_enumset1(A,A,B,C,D,E,F) = k4_enumset1(A,B,C,D,E,F) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

tff(f_45,axiom,(
    ! [A,B,C,D,E,F,G] : k6_enumset1(A,A,B,C,D,E,F,G) = k5_enumset1(A,B,C,D,E,F,G) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

tff(f_75,axiom,(
    ! [A,B,C,D,E,F,G,H,I] :
      ( I = k6_enumset1(A,B,C,D,E,F,G,H)
    <=> ! [J] :
          ( r2_hidden(J,I)
        <=> ~ ( J != A
              & J != B
              & J != C
              & J != D
              & J != E
              & J != F
              & J != G
              & J != H ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_enumset1)).

tff(f_77,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_85,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(k1_setfam_1(B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_setfam_1)).

tff(f_115,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => ! [C] :
                ( v1_relat_1(C)
               => r1_tarski(k5_relat_1(A,k3_xboole_0(B,C)),k3_xboole_0(k5_relat_1(A,B),k5_relat_1(A,C))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_81,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_92,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_104,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => ( r1_tarski(A,B)
               => r1_tarski(k5_relat_1(C,A),k5_relat_1(C,B)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_relat_1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C) )
     => r1_tarski(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).

tff(c_6,plain,(
    ! [A_6,B_7] : k1_enumset1(A_6,A_6,B_7) = k2_tarski(A_6,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_8,plain,(
    ! [A_8,B_9,C_10] : k2_enumset1(A_8,A_8,B_9,C_10) = k1_enumset1(A_8,B_9,C_10) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_10,plain,(
    ! [A_11,B_12,C_13,D_14] : k3_enumset1(A_11,A_11,B_12,C_13,D_14) = k2_enumset1(A_11,B_12,C_13,D_14) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_12,plain,(
    ! [B_16,A_15,D_18,E_19,C_17] : k4_enumset1(A_15,A_15,B_16,C_17,D_18,E_19) = k3_enumset1(A_15,B_16,C_17,D_18,E_19) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_14,plain,(
    ! [C_22,D_23,A_20,B_21,F_25,E_24] : k5_enumset1(A_20,A_20,B_21,C_22,D_23,E_24,F_25) = k4_enumset1(A_20,B_21,C_22,D_23,E_24,F_25) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_299,plain,(
    ! [B_278,A_279,G_283,C_281,E_282,F_280,D_277] : k6_enumset1(A_279,A_279,B_278,C_281,D_277,E_282,F_280,G_283) = k5_enumset1(A_279,B_278,C_281,D_277,E_282,F_280,G_283) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_20,plain,(
    ! [D_36,G_39,J_44,F_38,E_37,A_33,B_34,C_35] : r2_hidden(J_44,k6_enumset1(A_33,B_34,C_35,D_36,E_37,F_38,G_39,J_44)) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_345,plain,(
    ! [A_285,C_290,B_289,D_287,F_291,G_286,E_288] : r2_hidden(G_286,k5_enumset1(A_285,B_289,C_290,D_287,E_288,F_291,G_286)) ),
    inference(superposition,[status(thm),theory(equality)],[c_299,c_20])).

tff(c_352,plain,(
    ! [A_296,B_293,F_297,C_292,D_294,E_295] : r2_hidden(F_297,k4_enumset1(A_296,B_293,C_292,D_294,E_295,F_297)) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_345])).

tff(c_369,plain,(
    ! [B_301,A_303,C_299,E_302,D_300] : r2_hidden(E_302,k3_enumset1(A_303,B_301,C_299,D_300,E_302)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_352])).

tff(c_376,plain,(
    ! [D_304,A_305,B_306,C_307] : r2_hidden(D_304,k2_enumset1(A_305,B_306,C_307,D_304)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_369])).

tff(c_383,plain,(
    ! [C_308,A_309,B_310] : r2_hidden(C_308,k1_enumset1(A_309,B_310,C_308)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_376])).

tff(c_390,plain,(
    ! [B_311,A_312] : r2_hidden(B_311,k2_tarski(A_312,B_311)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_383])).

tff(c_99,plain,(
    ! [A_73,B_74] : k1_setfam_1(k2_tarski(A_73,B_74)) = k3_xboole_0(A_73,B_74) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_78,plain,(
    ! [B_50,A_49] :
      ( r1_tarski(k1_setfam_1(B_50),A_49)
      | ~ r2_hidden(A_49,B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_105,plain,(
    ! [A_73,B_74,A_49] :
      ( r1_tarski(k3_xboole_0(A_73,B_74),A_49)
      | ~ r2_hidden(A_49,k2_tarski(A_73,B_74)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_99,c_78])).

tff(c_396,plain,(
    ! [A_312,B_311] : r1_tarski(k3_xboole_0(A_312,B_311),B_311) ),
    inference(resolution,[status(thm)],[c_390,c_105])).

tff(c_88,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_2,plain,(
    ! [A_1,B_2] : r1_tarski(k3_xboole_0(A_1,B_2),A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_76,plain,(
    ! [A_47,B_48] :
      ( m1_subset_1(A_47,k1_zfmisc_1(B_48))
      | ~ r1_tarski(A_47,B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_120,plain,(
    ! [B_77,A_78] :
      ( v1_relat_1(B_77)
      | ~ m1_subset_1(B_77,k1_zfmisc_1(A_78))
      | ~ v1_relat_1(A_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_125,plain,(
    ! [A_79,B_80] :
      ( v1_relat_1(A_79)
      | ~ v1_relat_1(B_80)
      | ~ r1_tarski(A_79,B_80) ) ),
    inference(resolution,[status(thm)],[c_76,c_120])).

tff(c_133,plain,(
    ! [A_1,B_2] :
      ( v1_relat_1(k3_xboole_0(A_1,B_2))
      | ~ v1_relat_1(A_1) ) ),
    inference(resolution,[status(thm)],[c_2,c_125])).

tff(c_86,plain,(
    v1_relat_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_90,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_264,plain,(
    ! [C_273,A_274,B_275] :
      ( r1_tarski(k5_relat_1(C_273,A_274),k5_relat_1(C_273,B_275))
      | ~ r1_tarski(A_274,B_275)
      | ~ v1_relat_1(C_273)
      | ~ v1_relat_1(B_275)
      | ~ v1_relat_1(A_274) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_227,plain,(
    ! [C_240,A_241,B_242] :
      ( r1_tarski(k5_relat_1(C_240,A_241),k5_relat_1(C_240,B_242))
      | ~ r1_tarski(A_241,B_242)
      | ~ v1_relat_1(C_240)
      | ~ v1_relat_1(B_242)
      | ~ v1_relat_1(A_241) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_187,plain,(
    ! [A_159,B_160,C_161] :
      ( r1_tarski(A_159,k3_xboole_0(B_160,C_161))
      | ~ r1_tarski(A_159,C_161)
      | ~ r1_tarski(A_159,B_160) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_84,plain,(
    ~ r1_tarski(k5_relat_1('#skF_3',k3_xboole_0('#skF_4','#skF_5')),k3_xboole_0(k5_relat_1('#skF_3','#skF_4'),k5_relat_1('#skF_3','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_195,plain,
    ( ~ r1_tarski(k5_relat_1('#skF_3',k3_xboole_0('#skF_4','#skF_5')),k5_relat_1('#skF_3','#skF_5'))
    | ~ r1_tarski(k5_relat_1('#skF_3',k3_xboole_0('#skF_4','#skF_5')),k5_relat_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_187,c_84])).

tff(c_210,plain,(
    ~ r1_tarski(k5_relat_1('#skF_3',k3_xboole_0('#skF_4','#skF_5')),k5_relat_1('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_195])).

tff(c_230,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_4','#skF_5'),'#skF_4')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_4')
    | ~ v1_relat_1(k3_xboole_0('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_227,c_210])).

tff(c_236,plain,(
    ~ v1_relat_1(k3_xboole_0('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_90,c_2,c_230])).

tff(c_240,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_133,c_236])).

tff(c_244,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_240])).

tff(c_245,plain,(
    ~ r1_tarski(k5_relat_1('#skF_3',k3_xboole_0('#skF_4','#skF_5')),k5_relat_1('#skF_3','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_195])).

tff(c_267,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_4','#skF_5'),'#skF_5')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_5')
    | ~ v1_relat_1(k3_xboole_0('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_264,c_245])).

tff(c_273,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_4','#skF_5'),'#skF_5')
    | ~ v1_relat_1(k3_xboole_0('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_90,c_267])).

tff(c_275,plain,(
    ~ v1_relat_1(k3_xboole_0('#skF_4','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_273])).

tff(c_278,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_133,c_275])).

tff(c_282,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_278])).

tff(c_283,plain,(
    ~ r1_tarski(k3_xboole_0('#skF_4','#skF_5'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_273])).

tff(c_401,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_396,c_283])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:02:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.12/1.45  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.12/1.46  
% 3.12/1.46  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.12/1.46  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_setfam_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 3.12/1.46  
% 3.12/1.46  %Foreground sorts:
% 3.12/1.46  
% 3.12/1.46  
% 3.12/1.46  %Background operators:
% 3.12/1.46  
% 3.12/1.46  
% 3.12/1.46  %Foreground operators:
% 3.12/1.46  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.12/1.46  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.12/1.46  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.12/1.46  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.12/1.46  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.12/1.46  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.12/1.46  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.12/1.46  tff('#skF_5', type, '#skF_5': $i).
% 3.12/1.46  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.12/1.46  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.12/1.46  tff('#skF_3', type, '#skF_3': $i).
% 3.12/1.46  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.12/1.46  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.12/1.46  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.12/1.46  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.12/1.46  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.12/1.46  tff('#skF_4', type, '#skF_4': $i).
% 3.12/1.46  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.12/1.46  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.12/1.46  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.12/1.46  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.12/1.46  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.12/1.46  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.12/1.46  
% 3.17/1.48  tff(f_35, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 3.17/1.48  tff(f_37, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 3.17/1.48  tff(f_39, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 3.17/1.48  tff(f_41, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 3.17/1.48  tff(f_43, axiom, (![A, B, C, D, E, F]: (k5_enumset1(A, A, B, C, D, E, F) = k4_enumset1(A, B, C, D, E, F))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_enumset1)).
% 3.17/1.48  tff(f_45, axiom, (![A, B, C, D, E, F, G]: (k6_enumset1(A, A, B, C, D, E, F, G) = k5_enumset1(A, B, C, D, E, F, G))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t75_enumset1)).
% 3.17/1.48  tff(f_75, axiom, (![A, B, C, D, E, F, G, H, I]: ((I = k6_enumset1(A, B, C, D, E, F, G, H)) <=> (![J]: (r2_hidden(J, I) <=> ~(((((((~(J = A) & ~(J = B)) & ~(J = C)) & ~(J = D)) & ~(J = E)) & ~(J = F)) & ~(J = G)) & ~(J = H)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_enumset1)).
% 3.17/1.48  tff(f_77, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 3.17/1.48  tff(f_85, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(k1_setfam_1(B), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_setfam_1)).
% 3.17/1.48  tff(f_115, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => r1_tarski(k5_relat_1(A, k3_xboole_0(B, C)), k3_xboole_0(k5_relat_1(A, B), k5_relat_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_relat_1)).
% 3.17/1.48  tff(f_27, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 3.17/1.48  tff(f_81, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.17/1.48  tff(f_92, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.17/1.48  tff(f_104, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (r1_tarski(A, B) => r1_tarski(k5_relat_1(C, A), k5_relat_1(C, B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_relat_1)).
% 3.17/1.48  tff(f_33, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(A, C)) => r1_tarski(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_xboole_1)).
% 3.17/1.48  tff(c_6, plain, (![A_6, B_7]: (k1_enumset1(A_6, A_6, B_7)=k2_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.17/1.48  tff(c_8, plain, (![A_8, B_9, C_10]: (k2_enumset1(A_8, A_8, B_9, C_10)=k1_enumset1(A_8, B_9, C_10))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.17/1.48  tff(c_10, plain, (![A_11, B_12, C_13, D_14]: (k3_enumset1(A_11, A_11, B_12, C_13, D_14)=k2_enumset1(A_11, B_12, C_13, D_14))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.17/1.48  tff(c_12, plain, (![B_16, A_15, D_18, E_19, C_17]: (k4_enumset1(A_15, A_15, B_16, C_17, D_18, E_19)=k3_enumset1(A_15, B_16, C_17, D_18, E_19))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.17/1.48  tff(c_14, plain, (![C_22, D_23, A_20, B_21, F_25, E_24]: (k5_enumset1(A_20, A_20, B_21, C_22, D_23, E_24, F_25)=k4_enumset1(A_20, B_21, C_22, D_23, E_24, F_25))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.17/1.48  tff(c_299, plain, (![B_278, A_279, G_283, C_281, E_282, F_280, D_277]: (k6_enumset1(A_279, A_279, B_278, C_281, D_277, E_282, F_280, G_283)=k5_enumset1(A_279, B_278, C_281, D_277, E_282, F_280, G_283))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.17/1.48  tff(c_20, plain, (![D_36, G_39, J_44, F_38, E_37, A_33, B_34, C_35]: (r2_hidden(J_44, k6_enumset1(A_33, B_34, C_35, D_36, E_37, F_38, G_39, J_44)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.17/1.48  tff(c_345, plain, (![A_285, C_290, B_289, D_287, F_291, G_286, E_288]: (r2_hidden(G_286, k5_enumset1(A_285, B_289, C_290, D_287, E_288, F_291, G_286)))), inference(superposition, [status(thm), theory('equality')], [c_299, c_20])).
% 3.17/1.48  tff(c_352, plain, (![A_296, B_293, F_297, C_292, D_294, E_295]: (r2_hidden(F_297, k4_enumset1(A_296, B_293, C_292, D_294, E_295, F_297)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_345])).
% 3.17/1.48  tff(c_369, plain, (![B_301, A_303, C_299, E_302, D_300]: (r2_hidden(E_302, k3_enumset1(A_303, B_301, C_299, D_300, E_302)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_352])).
% 3.17/1.48  tff(c_376, plain, (![D_304, A_305, B_306, C_307]: (r2_hidden(D_304, k2_enumset1(A_305, B_306, C_307, D_304)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_369])).
% 3.17/1.48  tff(c_383, plain, (![C_308, A_309, B_310]: (r2_hidden(C_308, k1_enumset1(A_309, B_310, C_308)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_376])).
% 3.17/1.48  tff(c_390, plain, (![B_311, A_312]: (r2_hidden(B_311, k2_tarski(A_312, B_311)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_383])).
% 3.17/1.48  tff(c_99, plain, (![A_73, B_74]: (k1_setfam_1(k2_tarski(A_73, B_74))=k3_xboole_0(A_73, B_74))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.17/1.48  tff(c_78, plain, (![B_50, A_49]: (r1_tarski(k1_setfam_1(B_50), A_49) | ~r2_hidden(A_49, B_50))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.17/1.48  tff(c_105, plain, (![A_73, B_74, A_49]: (r1_tarski(k3_xboole_0(A_73, B_74), A_49) | ~r2_hidden(A_49, k2_tarski(A_73, B_74)))), inference(superposition, [status(thm), theory('equality')], [c_99, c_78])).
% 3.17/1.48  tff(c_396, plain, (![A_312, B_311]: (r1_tarski(k3_xboole_0(A_312, B_311), B_311))), inference(resolution, [status(thm)], [c_390, c_105])).
% 3.17/1.48  tff(c_88, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_115])).
% 3.17/1.48  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(k3_xboole_0(A_1, B_2), A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.17/1.48  tff(c_76, plain, (![A_47, B_48]: (m1_subset_1(A_47, k1_zfmisc_1(B_48)) | ~r1_tarski(A_47, B_48))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.17/1.48  tff(c_120, plain, (![B_77, A_78]: (v1_relat_1(B_77) | ~m1_subset_1(B_77, k1_zfmisc_1(A_78)) | ~v1_relat_1(A_78))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.17/1.48  tff(c_125, plain, (![A_79, B_80]: (v1_relat_1(A_79) | ~v1_relat_1(B_80) | ~r1_tarski(A_79, B_80))), inference(resolution, [status(thm)], [c_76, c_120])).
% 3.17/1.48  tff(c_133, plain, (![A_1, B_2]: (v1_relat_1(k3_xboole_0(A_1, B_2)) | ~v1_relat_1(A_1))), inference(resolution, [status(thm)], [c_2, c_125])).
% 3.17/1.48  tff(c_86, plain, (v1_relat_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_115])).
% 3.17/1.48  tff(c_90, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_115])).
% 3.17/1.48  tff(c_264, plain, (![C_273, A_274, B_275]: (r1_tarski(k5_relat_1(C_273, A_274), k5_relat_1(C_273, B_275)) | ~r1_tarski(A_274, B_275) | ~v1_relat_1(C_273) | ~v1_relat_1(B_275) | ~v1_relat_1(A_274))), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.17/1.48  tff(c_227, plain, (![C_240, A_241, B_242]: (r1_tarski(k5_relat_1(C_240, A_241), k5_relat_1(C_240, B_242)) | ~r1_tarski(A_241, B_242) | ~v1_relat_1(C_240) | ~v1_relat_1(B_242) | ~v1_relat_1(A_241))), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.17/1.48  tff(c_187, plain, (![A_159, B_160, C_161]: (r1_tarski(A_159, k3_xboole_0(B_160, C_161)) | ~r1_tarski(A_159, C_161) | ~r1_tarski(A_159, B_160))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.17/1.48  tff(c_84, plain, (~r1_tarski(k5_relat_1('#skF_3', k3_xboole_0('#skF_4', '#skF_5')), k3_xboole_0(k5_relat_1('#skF_3', '#skF_4'), k5_relat_1('#skF_3', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_115])).
% 3.17/1.48  tff(c_195, plain, (~r1_tarski(k5_relat_1('#skF_3', k3_xboole_0('#skF_4', '#skF_5')), k5_relat_1('#skF_3', '#skF_5')) | ~r1_tarski(k5_relat_1('#skF_3', k3_xboole_0('#skF_4', '#skF_5')), k5_relat_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_187, c_84])).
% 3.17/1.48  tff(c_210, plain, (~r1_tarski(k5_relat_1('#skF_3', k3_xboole_0('#skF_4', '#skF_5')), k5_relat_1('#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_195])).
% 3.17/1.48  tff(c_230, plain, (~r1_tarski(k3_xboole_0('#skF_4', '#skF_5'), '#skF_4') | ~v1_relat_1('#skF_3') | ~v1_relat_1('#skF_4') | ~v1_relat_1(k3_xboole_0('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_227, c_210])).
% 3.17/1.48  tff(c_236, plain, (~v1_relat_1(k3_xboole_0('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_90, c_2, c_230])).
% 3.17/1.48  tff(c_240, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_133, c_236])).
% 3.17/1.48  tff(c_244, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_88, c_240])).
% 3.17/1.48  tff(c_245, plain, (~r1_tarski(k5_relat_1('#skF_3', k3_xboole_0('#skF_4', '#skF_5')), k5_relat_1('#skF_3', '#skF_5'))), inference(splitRight, [status(thm)], [c_195])).
% 3.17/1.48  tff(c_267, plain, (~r1_tarski(k3_xboole_0('#skF_4', '#skF_5'), '#skF_5') | ~v1_relat_1('#skF_3') | ~v1_relat_1('#skF_5') | ~v1_relat_1(k3_xboole_0('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_264, c_245])).
% 3.17/1.48  tff(c_273, plain, (~r1_tarski(k3_xboole_0('#skF_4', '#skF_5'), '#skF_5') | ~v1_relat_1(k3_xboole_0('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_90, c_267])).
% 3.17/1.48  tff(c_275, plain, (~v1_relat_1(k3_xboole_0('#skF_4', '#skF_5'))), inference(splitLeft, [status(thm)], [c_273])).
% 3.17/1.48  tff(c_278, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_133, c_275])).
% 3.17/1.48  tff(c_282, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_88, c_278])).
% 3.17/1.48  tff(c_283, plain, (~r1_tarski(k3_xboole_0('#skF_4', '#skF_5'), '#skF_5')), inference(splitRight, [status(thm)], [c_273])).
% 3.17/1.48  tff(c_401, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_396, c_283])).
% 3.17/1.48  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.17/1.48  
% 3.17/1.48  Inference rules
% 3.17/1.48  ----------------------
% 3.17/1.48  #Ref     : 0
% 3.17/1.48  #Sup     : 68
% 3.17/1.48  #Fact    : 0
% 3.17/1.48  #Define  : 0
% 3.17/1.48  #Split   : 3
% 3.17/1.48  #Chain   : 0
% 3.17/1.48  #Close   : 0
% 3.17/1.48  
% 3.17/1.48  Ordering : KBO
% 3.17/1.48  
% 3.17/1.48  Simplification rules
% 3.17/1.48  ----------------------
% 3.17/1.48  #Subsume      : 1
% 3.17/1.48  #Demod        : 10
% 3.17/1.48  #Tautology    : 17
% 3.17/1.48  #SimpNegUnit  : 0
% 3.17/1.48  #BackRed      : 1
% 3.17/1.48  
% 3.17/1.48  #Partial instantiations: 0
% 3.17/1.48  #Strategies tried      : 1
% 3.17/1.48  
% 3.17/1.48  Timing (in seconds)
% 3.17/1.48  ----------------------
% 3.17/1.48  Preprocessing        : 0.35
% 3.17/1.48  Parsing              : 0.17
% 3.17/1.48  CNF conversion       : 0.03
% 3.17/1.48  Main loop            : 0.30
% 3.17/1.48  Inferencing          : 0.09
% 3.17/1.48  Reduction            : 0.08
% 3.17/1.48  Demodulation         : 0.06
% 3.17/1.48  BG Simplification    : 0.02
% 3.17/1.48  Subsumption          : 0.09
% 3.17/1.48  Abstraction          : 0.02
% 3.17/1.48  MUC search           : 0.00
% 3.17/1.48  Cooper               : 0.00
% 3.17/1.48  Total                : 0.68
% 3.17/1.48  Index Insertion      : 0.00
% 3.17/1.48  Index Deletion       : 0.00
% 3.17/1.48  Index Matching       : 0.00
% 3.17/1.48  BG Taut test         : 0.00
%------------------------------------------------------------------------------
