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
% DateTime   : Thu Dec  3 10:06:26 EST 2020

% Result     : Theorem 6.68s
% Output     : CNFRefutation 6.68s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 139 expanded)
%              Number of leaves         :   22 (  53 expanded)
%              Depth                    :   11
%              Number of atoms          :  185 ( 425 expanded)
%              Number of equality atoms :   26 (  79 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > r1_ordinal1 > v4_ordinal1 > v3_ordinal1 > v1_xboole_0 > #nlpp > k1_ordinal1 > #skF_1 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k1_ordinal1,type,(
    k1_ordinal1: $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r1_ordinal1,type,(
    r1_ordinal1: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v3_ordinal1,type,(
    v3_ordinal1: $i > $o )).

tff(v4_ordinal1,type,(
    v4_ordinal1: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_105,negated_conjecture,(
    ~ ! [A] :
        ( v3_ordinal1(A)
       => ( ~ ( ~ v4_ordinal1(A)
              & ! [B] :
                  ( v3_ordinal1(B)
                 => A != k1_ordinal1(B) ) )
          & ~ ( ? [B] :
                  ( v3_ordinal1(B)
                  & A = k1_ordinal1(B) )
              & v4_ordinal1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_ordinal1)).

tff(f_84,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ( v4_ordinal1(A)
      <=> ! [B] :
            ( v3_ordinal1(B)
           => ( r2_hidden(B,A)
             => r2_hidden(k1_ordinal1(B),A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_ordinal1)).

tff(f_38,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ( ~ v1_xboole_0(k1_ordinal1(A))
        & v3_ordinal1(k1_ordinal1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_ordinal1)).

tff(f_64,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ( r2_hidden(A,B)
          <=> r1_ordinal1(k1_ordinal1(A),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_ordinal1)).

tff(f_73,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ( r2_hidden(A,k1_ordinal1(B))
          <=> r1_ordinal1(A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_ordinal1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( r2_hidden(A,k1_ordinal1(B))
    <=> ( r2_hidden(A,B)
        | A = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_ordinal1)).

tff(f_55,axiom,(
    ! [A] : A != k1_ordinal1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_ordinal1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( ( v3_ordinal1(A)
        & v3_ordinal1(B) )
     => ( r1_ordinal1(A,B)
      <=> r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_40,plain,(
    v3_ordinal1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_38,plain,(
    ! [A_15] :
      ( v3_ordinal1('#skF_1'(A_15))
      | v4_ordinal1(A_15)
      | ~ v3_ordinal1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_36,plain,(
    ! [A_15] :
      ( r2_hidden('#skF_1'(A_15),A_15)
      | v4_ordinal1(A_15)
      | ~ v3_ordinal1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_8,plain,(
    ! [A_3] :
      ( v3_ordinal1(k1_ordinal1(A_3))
      | ~ v3_ordinal1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_26,plain,(
    ! [A_9,B_11] :
      ( r1_ordinal1(k1_ordinal1(A_9),B_11)
      | ~ r2_hidden(A_9,B_11)
      | ~ v3_ordinal1(B_11)
      | ~ v3_ordinal1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_2096,plain,(
    ! [A_174,B_175] :
      ( r2_hidden(A_174,k1_ordinal1(B_175))
      | ~ r1_ordinal1(A_174,B_175)
      | ~ v3_ordinal1(B_175)
      | ~ v3_ordinal1(A_174) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_16,plain,(
    ! [B_7,A_6] :
      ( B_7 = A_6
      | r2_hidden(A_6,B_7)
      | ~ r2_hidden(A_6,k1_ordinal1(B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_2125,plain,(
    ! [B_179,A_180] :
      ( B_179 = A_180
      | r2_hidden(A_180,B_179)
      | ~ r1_ordinal1(A_180,B_179)
      | ~ v3_ordinal1(B_179)
      | ~ v3_ordinal1(A_180) ) ),
    inference(resolution,[status(thm)],[c_2096,c_16])).

tff(c_34,plain,(
    ! [A_15] :
      ( ~ r2_hidden(k1_ordinal1('#skF_1'(A_15)),A_15)
      | v4_ordinal1(A_15)
      | ~ v3_ordinal1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_2765,plain,(
    ! [B_226] :
      ( v4_ordinal1(B_226)
      | k1_ordinal1('#skF_1'(B_226)) = B_226
      | ~ r1_ordinal1(k1_ordinal1('#skF_1'(B_226)),B_226)
      | ~ v3_ordinal1(B_226)
      | ~ v3_ordinal1(k1_ordinal1('#skF_1'(B_226))) ) ),
    inference(resolution,[status(thm)],[c_2125,c_34])).

tff(c_3599,plain,(
    ! [B_259] :
      ( v4_ordinal1(B_259)
      | k1_ordinal1('#skF_1'(B_259)) = B_259
      | ~ v3_ordinal1(k1_ordinal1('#skF_1'(B_259)))
      | ~ r2_hidden('#skF_1'(B_259),B_259)
      | ~ v3_ordinal1(B_259)
      | ~ v3_ordinal1('#skF_1'(B_259)) ) ),
    inference(resolution,[status(thm)],[c_26,c_2765])).

tff(c_3606,plain,(
    ! [B_260] :
      ( v4_ordinal1(B_260)
      | k1_ordinal1('#skF_1'(B_260)) = B_260
      | ~ r2_hidden('#skF_1'(B_260),B_260)
      | ~ v3_ordinal1(B_260)
      | ~ v3_ordinal1('#skF_1'(B_260)) ) ),
    inference(resolution,[status(thm)],[c_8,c_3599])).

tff(c_3641,plain,(
    ! [A_261] :
      ( k1_ordinal1('#skF_1'(A_261)) = A_261
      | ~ v3_ordinal1('#skF_1'(A_261))
      | v4_ordinal1(A_261)
      | ~ v3_ordinal1(A_261) ) ),
    inference(resolution,[status(thm)],[c_36,c_3606])).

tff(c_3649,plain,(
    ! [A_262] :
      ( k1_ordinal1('#skF_1'(A_262)) = A_262
      | v4_ordinal1(A_262)
      | ~ v3_ordinal1(A_262) ) ),
    inference(resolution,[status(thm)],[c_38,c_3641])).

tff(c_2000,plain,(
    ! [A_150] :
      ( v3_ordinal1('#skF_1'(A_150))
      | v4_ordinal1(A_150)
      | ~ v3_ordinal1(A_150) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_52,plain,
    ( ~ v4_ordinal1('#skF_2')
    | v3_ordinal1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_57,plain,(
    ~ v4_ordinal1('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_42,plain,(
    ! [B_21] :
      ( k1_ordinal1(B_21) != '#skF_2'
      | ~ v3_ordinal1(B_21)
      | v4_ordinal1('#skF_2') ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_1985,plain,(
    ! [B_21] :
      ( k1_ordinal1(B_21) != '#skF_2'
      | ~ v3_ordinal1(B_21) ) ),
    inference(negUnitSimplification,[status(thm)],[c_57,c_42])).

tff(c_2004,plain,(
    ! [A_150] :
      ( k1_ordinal1('#skF_1'(A_150)) != '#skF_2'
      | v4_ordinal1(A_150)
      | ~ v3_ordinal1(A_150) ) ),
    inference(resolution,[status(thm)],[c_2000,c_1985])).

tff(c_3813,plain,(
    ! [A_262] :
      ( A_262 != '#skF_2'
      | v4_ordinal1(A_262)
      | ~ v3_ordinal1(A_262)
      | v4_ordinal1(A_262)
      | ~ v3_ordinal1(A_262) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3649,c_2004])).

tff(c_3859,plain,(
    ! [A_264] :
      ( A_264 != '#skF_2'
      | ~ v3_ordinal1(A_264)
      | v4_ordinal1(A_264) ) ),
    inference(factorization,[status(thm),theory(equality)],[c_3813])).

tff(c_3865,plain,(
    ~ v3_ordinal1('#skF_2') ),
    inference(resolution,[status(thm)],[c_3859,c_57])).

tff(c_3870,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_3865])).

tff(c_3872,plain,(
    v4_ordinal1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_48,plain,
    ( ~ v4_ordinal1('#skF_2')
    | k1_ordinal1('#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_3876,plain,(
    k1_ordinal1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3872,c_48])).

tff(c_22,plain,(
    ! [A_8] : k1_ordinal1(A_8) != A_8 ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_3889,plain,(
    '#skF_2' != '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_3876,c_22])).

tff(c_3871,plain,(
    v3_ordinal1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_18,plain,(
    ! [B_7] : r2_hidden(B_7,k1_ordinal1(B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_3886,plain,(
    r2_hidden('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_3876,c_18])).

tff(c_20,plain,(
    ! [A_6,B_7] :
      ( ~ r2_hidden(A_6,B_7)
      | r2_hidden(A_6,k1_ordinal1(B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_4002,plain,(
    ! [A_286,B_287] :
      ( r1_ordinal1(A_286,B_287)
      | ~ r2_hidden(A_286,k1_ordinal1(B_287))
      | ~ v3_ordinal1(B_287)
      | ~ v3_ordinal1(A_286) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_4076,plain,(
    ! [A_290,B_291] :
      ( r1_ordinal1(A_290,B_291)
      | ~ v3_ordinal1(B_291)
      | ~ v3_ordinal1(A_290)
      | ~ r2_hidden(A_290,B_291) ) ),
    inference(resolution,[status(thm)],[c_20,c_4002])).

tff(c_4091,plain,
    ( r1_ordinal1('#skF_3','#skF_2')
    | ~ v3_ordinal1('#skF_2')
    | ~ v3_ordinal1('#skF_3') ),
    inference(resolution,[status(thm)],[c_3886,c_4076])).

tff(c_4105,plain,(
    r1_ordinal1('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3871,c_40,c_4091])).

tff(c_4328,plain,(
    ! [B_306,A_307] :
      ( r2_hidden(k1_ordinal1(B_306),A_307)
      | ~ r2_hidden(B_306,A_307)
      | ~ v3_ordinal1(B_306)
      | ~ v4_ordinal1(A_307)
      | ~ v3_ordinal1(A_307) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_4362,plain,(
    ! [A_307] :
      ( r2_hidden('#skF_2',A_307)
      | ~ r2_hidden('#skF_3',A_307)
      | ~ v3_ordinal1('#skF_3')
      | ~ v4_ordinal1(A_307)
      | ~ v3_ordinal1(A_307) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3876,c_4328])).

tff(c_4381,plain,(
    ! [A_308] :
      ( r2_hidden('#skF_2',A_308)
      | ~ r2_hidden('#skF_3',A_308)
      | ~ v4_ordinal1(A_308)
      | ~ v3_ordinal1(A_308) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3871,c_4362])).

tff(c_4016,plain,(
    ! [A_286] :
      ( r1_ordinal1(A_286,'#skF_3')
      | ~ r2_hidden(A_286,'#skF_2')
      | ~ v3_ordinal1('#skF_3')
      | ~ v3_ordinal1(A_286) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3876,c_4002])).

tff(c_4026,plain,(
    ! [A_286] :
      ( r1_ordinal1(A_286,'#skF_3')
      | ~ r2_hidden(A_286,'#skF_2')
      | ~ v3_ordinal1(A_286) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3871,c_4016])).

tff(c_4396,plain,
    ( r1_ordinal1('#skF_2','#skF_3')
    | ~ r2_hidden('#skF_3','#skF_2')
    | ~ v4_ordinal1('#skF_2')
    | ~ v3_ordinal1('#skF_2') ),
    inference(resolution,[status(thm)],[c_4381,c_4026])).

tff(c_4420,plain,(
    r1_ordinal1('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_3872,c_3886,c_4396])).

tff(c_14,plain,(
    ! [A_4,B_5] :
      ( r1_tarski(A_4,B_5)
      | ~ r1_ordinal1(A_4,B_5)
      | ~ v3_ordinal1(B_5)
      | ~ v3_ordinal1(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_3962,plain,(
    ! [A_278,B_279] :
      ( r1_tarski(A_278,B_279)
      | ~ r1_ordinal1(A_278,B_279)
      | ~ v3_ordinal1(B_279)
      | ~ v3_ordinal1(A_278) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_4646,plain,(
    ! [B_315,A_316] :
      ( B_315 = A_316
      | ~ r1_tarski(B_315,A_316)
      | ~ r1_ordinal1(A_316,B_315)
      | ~ v3_ordinal1(B_315)
      | ~ v3_ordinal1(A_316) ) ),
    inference(resolution,[status(thm)],[c_3962,c_2])).

tff(c_5556,plain,(
    ! [B_340,A_341] :
      ( B_340 = A_341
      | ~ r1_ordinal1(B_340,A_341)
      | ~ r1_ordinal1(A_341,B_340)
      | ~ v3_ordinal1(B_340)
      | ~ v3_ordinal1(A_341) ) ),
    inference(resolution,[status(thm)],[c_14,c_4646])).

tff(c_5572,plain,
    ( '#skF_2' = '#skF_3'
    | ~ r1_ordinal1('#skF_3','#skF_2')
    | ~ v3_ordinal1('#skF_2')
    | ~ v3_ordinal1('#skF_3') ),
    inference(resolution,[status(thm)],[c_4420,c_5556])).

tff(c_5615,plain,(
    '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3871,c_40,c_4105,c_5572])).

tff(c_5617,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3889,c_5615])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n006.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 10:20:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.68/2.25  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.68/2.26  
% 6.68/2.26  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.68/2.26  %$ r2_hidden > r1_tarski > r1_ordinal1 > v4_ordinal1 > v3_ordinal1 > v1_xboole_0 > #nlpp > k1_ordinal1 > #skF_1 > #skF_2 > #skF_3
% 6.68/2.26  
% 6.68/2.26  %Foreground sorts:
% 6.68/2.26  
% 6.68/2.26  
% 6.68/2.26  %Background operators:
% 6.68/2.26  
% 6.68/2.26  
% 6.68/2.26  %Foreground operators:
% 6.68/2.26  tff(k1_ordinal1, type, k1_ordinal1: $i > $i).
% 6.68/2.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.68/2.26  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.68/2.26  tff('#skF_1', type, '#skF_1': $i > $i).
% 6.68/2.26  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.68/2.26  tff(r1_ordinal1, type, r1_ordinal1: ($i * $i) > $o).
% 6.68/2.26  tff('#skF_2', type, '#skF_2': $i).
% 6.68/2.26  tff('#skF_3', type, '#skF_3': $i).
% 6.68/2.26  tff(v3_ordinal1, type, v3_ordinal1: $i > $o).
% 6.68/2.26  tff(v4_ordinal1, type, v4_ordinal1: $i > $o).
% 6.68/2.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.68/2.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.68/2.26  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 6.68/2.26  
% 6.68/2.27  tff(f_105, negated_conjecture, ~(![A]: (v3_ordinal1(A) => (~(~v4_ordinal1(A) & (![B]: (v3_ordinal1(B) => ~(A = k1_ordinal1(B))))) & ~((?[B]: (v3_ordinal1(B) & (A = k1_ordinal1(B)))) & v4_ordinal1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t42_ordinal1)).
% 6.68/2.27  tff(f_84, axiom, (![A]: (v3_ordinal1(A) => (v4_ordinal1(A) <=> (![B]: (v3_ordinal1(B) => (r2_hidden(B, A) => r2_hidden(k1_ordinal1(B), A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_ordinal1)).
% 6.68/2.27  tff(f_38, axiom, (![A]: (v3_ordinal1(A) => (~v1_xboole_0(k1_ordinal1(A)) & v3_ordinal1(k1_ordinal1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_ordinal1)).
% 6.68/2.27  tff(f_64, axiom, (![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r2_hidden(A, B) <=> r1_ordinal1(k1_ordinal1(A), B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t33_ordinal1)).
% 6.68/2.27  tff(f_73, axiom, (![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r2_hidden(A, k1_ordinal1(B)) <=> r1_ordinal1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_ordinal1)).
% 6.68/2.27  tff(f_52, axiom, (![A, B]: (r2_hidden(A, k1_ordinal1(B)) <=> (r2_hidden(A, B) | (A = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_ordinal1)).
% 6.68/2.27  tff(f_55, axiom, (![A]: ~(A = k1_ordinal1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_ordinal1)).
% 6.68/2.27  tff(f_46, axiom, (![A, B]: ((v3_ordinal1(A) & v3_ordinal1(B)) => (r1_ordinal1(A, B) <=> r1_tarski(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r1_ordinal1)).
% 6.68/2.27  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 6.68/2.27  tff(c_40, plain, (v3_ordinal1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_105])).
% 6.68/2.27  tff(c_38, plain, (![A_15]: (v3_ordinal1('#skF_1'(A_15)) | v4_ordinal1(A_15) | ~v3_ordinal1(A_15))), inference(cnfTransformation, [status(thm)], [f_84])).
% 6.68/2.27  tff(c_36, plain, (![A_15]: (r2_hidden('#skF_1'(A_15), A_15) | v4_ordinal1(A_15) | ~v3_ordinal1(A_15))), inference(cnfTransformation, [status(thm)], [f_84])).
% 6.68/2.27  tff(c_8, plain, (![A_3]: (v3_ordinal1(k1_ordinal1(A_3)) | ~v3_ordinal1(A_3))), inference(cnfTransformation, [status(thm)], [f_38])).
% 6.68/2.27  tff(c_26, plain, (![A_9, B_11]: (r1_ordinal1(k1_ordinal1(A_9), B_11) | ~r2_hidden(A_9, B_11) | ~v3_ordinal1(B_11) | ~v3_ordinal1(A_9))), inference(cnfTransformation, [status(thm)], [f_64])).
% 6.68/2.27  tff(c_2096, plain, (![A_174, B_175]: (r2_hidden(A_174, k1_ordinal1(B_175)) | ~r1_ordinal1(A_174, B_175) | ~v3_ordinal1(B_175) | ~v3_ordinal1(A_174))), inference(cnfTransformation, [status(thm)], [f_73])).
% 6.68/2.27  tff(c_16, plain, (![B_7, A_6]: (B_7=A_6 | r2_hidden(A_6, B_7) | ~r2_hidden(A_6, k1_ordinal1(B_7)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 6.68/2.27  tff(c_2125, plain, (![B_179, A_180]: (B_179=A_180 | r2_hidden(A_180, B_179) | ~r1_ordinal1(A_180, B_179) | ~v3_ordinal1(B_179) | ~v3_ordinal1(A_180))), inference(resolution, [status(thm)], [c_2096, c_16])).
% 6.68/2.27  tff(c_34, plain, (![A_15]: (~r2_hidden(k1_ordinal1('#skF_1'(A_15)), A_15) | v4_ordinal1(A_15) | ~v3_ordinal1(A_15))), inference(cnfTransformation, [status(thm)], [f_84])).
% 6.68/2.27  tff(c_2765, plain, (![B_226]: (v4_ordinal1(B_226) | k1_ordinal1('#skF_1'(B_226))=B_226 | ~r1_ordinal1(k1_ordinal1('#skF_1'(B_226)), B_226) | ~v3_ordinal1(B_226) | ~v3_ordinal1(k1_ordinal1('#skF_1'(B_226))))), inference(resolution, [status(thm)], [c_2125, c_34])).
% 6.68/2.27  tff(c_3599, plain, (![B_259]: (v4_ordinal1(B_259) | k1_ordinal1('#skF_1'(B_259))=B_259 | ~v3_ordinal1(k1_ordinal1('#skF_1'(B_259))) | ~r2_hidden('#skF_1'(B_259), B_259) | ~v3_ordinal1(B_259) | ~v3_ordinal1('#skF_1'(B_259)))), inference(resolution, [status(thm)], [c_26, c_2765])).
% 6.68/2.27  tff(c_3606, plain, (![B_260]: (v4_ordinal1(B_260) | k1_ordinal1('#skF_1'(B_260))=B_260 | ~r2_hidden('#skF_1'(B_260), B_260) | ~v3_ordinal1(B_260) | ~v3_ordinal1('#skF_1'(B_260)))), inference(resolution, [status(thm)], [c_8, c_3599])).
% 6.68/2.27  tff(c_3641, plain, (![A_261]: (k1_ordinal1('#skF_1'(A_261))=A_261 | ~v3_ordinal1('#skF_1'(A_261)) | v4_ordinal1(A_261) | ~v3_ordinal1(A_261))), inference(resolution, [status(thm)], [c_36, c_3606])).
% 6.68/2.27  tff(c_3649, plain, (![A_262]: (k1_ordinal1('#skF_1'(A_262))=A_262 | v4_ordinal1(A_262) | ~v3_ordinal1(A_262))), inference(resolution, [status(thm)], [c_38, c_3641])).
% 6.68/2.27  tff(c_2000, plain, (![A_150]: (v3_ordinal1('#skF_1'(A_150)) | v4_ordinal1(A_150) | ~v3_ordinal1(A_150))), inference(cnfTransformation, [status(thm)], [f_84])).
% 6.68/2.27  tff(c_52, plain, (~v4_ordinal1('#skF_2') | v3_ordinal1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_105])).
% 6.68/2.27  tff(c_57, plain, (~v4_ordinal1('#skF_2')), inference(splitLeft, [status(thm)], [c_52])).
% 6.68/2.27  tff(c_42, plain, (![B_21]: (k1_ordinal1(B_21)!='#skF_2' | ~v3_ordinal1(B_21) | v4_ordinal1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_105])).
% 6.68/2.27  tff(c_1985, plain, (![B_21]: (k1_ordinal1(B_21)!='#skF_2' | ~v3_ordinal1(B_21))), inference(negUnitSimplification, [status(thm)], [c_57, c_42])).
% 6.68/2.27  tff(c_2004, plain, (![A_150]: (k1_ordinal1('#skF_1'(A_150))!='#skF_2' | v4_ordinal1(A_150) | ~v3_ordinal1(A_150))), inference(resolution, [status(thm)], [c_2000, c_1985])).
% 6.68/2.27  tff(c_3813, plain, (![A_262]: (A_262!='#skF_2' | v4_ordinal1(A_262) | ~v3_ordinal1(A_262) | v4_ordinal1(A_262) | ~v3_ordinal1(A_262))), inference(superposition, [status(thm), theory('equality')], [c_3649, c_2004])).
% 6.68/2.27  tff(c_3859, plain, (![A_264]: (A_264!='#skF_2' | ~v3_ordinal1(A_264) | v4_ordinal1(A_264))), inference(factorization, [status(thm), theory('equality')], [c_3813])).
% 6.68/2.27  tff(c_3865, plain, (~v3_ordinal1('#skF_2')), inference(resolution, [status(thm)], [c_3859, c_57])).
% 6.68/2.27  tff(c_3870, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_3865])).
% 6.68/2.27  tff(c_3872, plain, (v4_ordinal1('#skF_2')), inference(splitRight, [status(thm)], [c_52])).
% 6.68/2.27  tff(c_48, plain, (~v4_ordinal1('#skF_2') | k1_ordinal1('#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_105])).
% 6.68/2.27  tff(c_3876, plain, (k1_ordinal1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_3872, c_48])).
% 6.68/2.27  tff(c_22, plain, (![A_8]: (k1_ordinal1(A_8)!=A_8)), inference(cnfTransformation, [status(thm)], [f_55])).
% 6.68/2.27  tff(c_3889, plain, ('#skF_2'!='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_3876, c_22])).
% 6.68/2.27  tff(c_3871, plain, (v3_ordinal1('#skF_3')), inference(splitRight, [status(thm)], [c_52])).
% 6.68/2.27  tff(c_18, plain, (![B_7]: (r2_hidden(B_7, k1_ordinal1(B_7)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 6.68/2.27  tff(c_3886, plain, (r2_hidden('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_3876, c_18])).
% 6.68/2.27  tff(c_20, plain, (![A_6, B_7]: (~r2_hidden(A_6, B_7) | r2_hidden(A_6, k1_ordinal1(B_7)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 6.68/2.27  tff(c_4002, plain, (![A_286, B_287]: (r1_ordinal1(A_286, B_287) | ~r2_hidden(A_286, k1_ordinal1(B_287)) | ~v3_ordinal1(B_287) | ~v3_ordinal1(A_286))), inference(cnfTransformation, [status(thm)], [f_73])).
% 6.68/2.27  tff(c_4076, plain, (![A_290, B_291]: (r1_ordinal1(A_290, B_291) | ~v3_ordinal1(B_291) | ~v3_ordinal1(A_290) | ~r2_hidden(A_290, B_291))), inference(resolution, [status(thm)], [c_20, c_4002])).
% 6.68/2.27  tff(c_4091, plain, (r1_ordinal1('#skF_3', '#skF_2') | ~v3_ordinal1('#skF_2') | ~v3_ordinal1('#skF_3')), inference(resolution, [status(thm)], [c_3886, c_4076])).
% 6.68/2.27  tff(c_4105, plain, (r1_ordinal1('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_3871, c_40, c_4091])).
% 6.68/2.27  tff(c_4328, plain, (![B_306, A_307]: (r2_hidden(k1_ordinal1(B_306), A_307) | ~r2_hidden(B_306, A_307) | ~v3_ordinal1(B_306) | ~v4_ordinal1(A_307) | ~v3_ordinal1(A_307))), inference(cnfTransformation, [status(thm)], [f_84])).
% 6.68/2.27  tff(c_4362, plain, (![A_307]: (r2_hidden('#skF_2', A_307) | ~r2_hidden('#skF_3', A_307) | ~v3_ordinal1('#skF_3') | ~v4_ordinal1(A_307) | ~v3_ordinal1(A_307))), inference(superposition, [status(thm), theory('equality')], [c_3876, c_4328])).
% 6.68/2.27  tff(c_4381, plain, (![A_308]: (r2_hidden('#skF_2', A_308) | ~r2_hidden('#skF_3', A_308) | ~v4_ordinal1(A_308) | ~v3_ordinal1(A_308))), inference(demodulation, [status(thm), theory('equality')], [c_3871, c_4362])).
% 6.68/2.27  tff(c_4016, plain, (![A_286]: (r1_ordinal1(A_286, '#skF_3') | ~r2_hidden(A_286, '#skF_2') | ~v3_ordinal1('#skF_3') | ~v3_ordinal1(A_286))), inference(superposition, [status(thm), theory('equality')], [c_3876, c_4002])).
% 6.68/2.27  tff(c_4026, plain, (![A_286]: (r1_ordinal1(A_286, '#skF_3') | ~r2_hidden(A_286, '#skF_2') | ~v3_ordinal1(A_286))), inference(demodulation, [status(thm), theory('equality')], [c_3871, c_4016])).
% 6.68/2.27  tff(c_4396, plain, (r1_ordinal1('#skF_2', '#skF_3') | ~r2_hidden('#skF_3', '#skF_2') | ~v4_ordinal1('#skF_2') | ~v3_ordinal1('#skF_2')), inference(resolution, [status(thm)], [c_4381, c_4026])).
% 6.68/2.27  tff(c_4420, plain, (r1_ordinal1('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_3872, c_3886, c_4396])).
% 6.68/2.27  tff(c_14, plain, (![A_4, B_5]: (r1_tarski(A_4, B_5) | ~r1_ordinal1(A_4, B_5) | ~v3_ordinal1(B_5) | ~v3_ordinal1(A_4))), inference(cnfTransformation, [status(thm)], [f_46])).
% 6.68/2.27  tff(c_3962, plain, (![A_278, B_279]: (r1_tarski(A_278, B_279) | ~r1_ordinal1(A_278, B_279) | ~v3_ordinal1(B_279) | ~v3_ordinal1(A_278))), inference(cnfTransformation, [status(thm)], [f_46])).
% 6.68/2.27  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.68/2.27  tff(c_4646, plain, (![B_315, A_316]: (B_315=A_316 | ~r1_tarski(B_315, A_316) | ~r1_ordinal1(A_316, B_315) | ~v3_ordinal1(B_315) | ~v3_ordinal1(A_316))), inference(resolution, [status(thm)], [c_3962, c_2])).
% 6.68/2.27  tff(c_5556, plain, (![B_340, A_341]: (B_340=A_341 | ~r1_ordinal1(B_340, A_341) | ~r1_ordinal1(A_341, B_340) | ~v3_ordinal1(B_340) | ~v3_ordinal1(A_341))), inference(resolution, [status(thm)], [c_14, c_4646])).
% 6.68/2.27  tff(c_5572, plain, ('#skF_2'='#skF_3' | ~r1_ordinal1('#skF_3', '#skF_2') | ~v3_ordinal1('#skF_2') | ~v3_ordinal1('#skF_3')), inference(resolution, [status(thm)], [c_4420, c_5556])).
% 6.68/2.27  tff(c_5615, plain, ('#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_3871, c_40, c_4105, c_5572])).
% 6.68/2.27  tff(c_5617, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3889, c_5615])).
% 6.68/2.27  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.68/2.27  
% 6.68/2.27  Inference rules
% 6.68/2.27  ----------------------
% 6.68/2.27  #Ref     : 0
% 6.68/2.27  #Sup     : 1135
% 6.68/2.27  #Fact    : 4
% 6.68/2.27  #Define  : 0
% 6.68/2.27  #Split   : 8
% 6.68/2.27  #Chain   : 0
% 6.68/2.27  #Close   : 0
% 6.68/2.27  
% 6.68/2.27  Ordering : KBO
% 6.68/2.27  
% 6.68/2.27  Simplification rules
% 6.68/2.27  ----------------------
% 6.68/2.27  #Subsume      : 342
% 6.68/2.27  #Demod        : 475
% 6.68/2.27  #Tautology    : 205
% 6.68/2.27  #SimpNegUnit  : 57
% 6.68/2.27  #BackRed      : 0
% 6.68/2.27  
% 6.68/2.27  #Partial instantiations: 0
% 6.68/2.27  #Strategies tried      : 1
% 6.68/2.27  
% 6.68/2.27  Timing (in seconds)
% 6.68/2.27  ----------------------
% 6.68/2.28  Preprocessing        : 0.29
% 6.68/2.28  Parsing              : 0.16
% 6.68/2.28  CNF conversion       : 0.02
% 6.68/2.28  Main loop            : 1.22
% 6.68/2.28  Inferencing          : 0.39
% 6.68/2.28  Reduction            : 0.29
% 6.68/2.28  Demodulation         : 0.18
% 6.68/2.28  BG Simplification    : 0.05
% 6.68/2.28  Subsumption          : 0.42
% 6.68/2.28  Abstraction          : 0.05
% 6.68/2.28  MUC search           : 0.00
% 6.68/2.28  Cooper               : 0.00
% 6.68/2.28  Total                : 1.55
% 6.68/2.28  Index Insertion      : 0.00
% 6.68/2.28  Index Deletion       : 0.00
% 6.68/2.28  Index Matching       : 0.00
% 6.68/2.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------
