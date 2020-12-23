%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:13 EST 2020

% Result     : Theorem 3.37s
% Output     : CNFRefutation 3.37s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 113 expanded)
%              Number of leaves         :   29 (  51 expanded)
%              Depth                    :    9
%              Number of atoms          :   90 ( 190 expanded)
%              Number of equality atoms :   21 (  38 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > m1_subset_1 > v1_relat_1 > k5_relat_1 > k4_xboole_0 > k4_tarski > k3_xboole_0 > #nlpp > k1_zfmisc_1 > o_0_0_xboole_0 > k1_xboole_0 > #skF_6 > #skF_2 > #skF_4 > #skF_5 > #skF_7 > #skF_8 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(o_0_0_xboole_0,type,(
    o_0_0_xboole_0: $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_88,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ( k5_relat_1(k1_xboole_0,A) = k1_xboole_0
          & k5_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_relat_1)).

tff(f_50,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_63,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_81,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => ( C = k5_relat_1(A,B)
              <=> ! [D,E] :
                    ( r2_hidden(k4_tarski(D,E),C)
                  <=> ? [F] :
                        ( r2_hidden(k4_tarski(D,F),A)
                        & r2_hidden(k4_tarski(F,E),B) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_relat_1)).

tff(f_48,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_42,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_40,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(c_40,plain,
    ( k5_relat_1('#skF_8',k1_xboole_0) != k1_xboole_0
    | k5_relat_1(k1_xboole_0,'#skF_8') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_75,plain,(
    k5_relat_1(k1_xboole_0,'#skF_8') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_42,plain,(
    v1_relat_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_16,plain,(
    ! [A_11] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_11)) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_65,plain,(
    ! [B_121,A_122] :
      ( v1_relat_1(B_121)
      | ~ m1_subset_1(B_121,k1_zfmisc_1(A_122))
      | ~ v1_relat_1(A_122) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_69,plain,(
    ! [A_11] :
      ( v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_11) ) ),
    inference(resolution,[status(thm)],[c_16,c_65])).

tff(c_70,plain,(
    ! [A_11] : ~ v1_relat_1(A_11) ),
    inference(splitLeft,[status(thm)],[c_69])).

tff(c_73,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_42])).

tff(c_74,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_69])).

tff(c_720,plain,(
    ! [A_190,B_191,C_192] :
      ( r2_hidden(k4_tarski('#skF_3'(A_190,B_191,C_192),'#skF_5'(A_190,B_191,C_192)),A_190)
      | r2_hidden(k4_tarski('#skF_6'(A_190,B_191,C_192),'#skF_7'(A_190,B_191,C_192)),C_192)
      | k5_relat_1(A_190,B_191) = C_192
      | ~ v1_relat_1(C_192)
      | ~ v1_relat_1(B_191)
      | ~ v1_relat_1(A_190) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_14,plain,(
    ! [A_10] : r1_xboole_0(A_10,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_8,plain,(
    ! [A_6] : k3_xboole_0(A_6,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_76,plain,(
    ! [A_123,B_124,C_125] :
      ( ~ r1_xboole_0(A_123,B_124)
      | ~ r2_hidden(C_125,k3_xboole_0(A_123,B_124)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_79,plain,(
    ! [A_6,C_125] :
      ( ~ r1_xboole_0(A_6,k1_xboole_0)
      | ~ r2_hidden(C_125,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_76])).

tff(c_81,plain,(
    ! [C_125] : ~ r2_hidden(C_125,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_79])).

tff(c_750,plain,(
    ! [A_190,B_191] :
      ( r2_hidden(k4_tarski('#skF_3'(A_190,B_191,k1_xboole_0),'#skF_5'(A_190,B_191,k1_xboole_0)),A_190)
      | k5_relat_1(A_190,B_191) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(B_191)
      | ~ v1_relat_1(A_190) ) ),
    inference(resolution,[status(thm)],[c_720,c_81])).

tff(c_766,plain,(
    ! [A_193,B_194] :
      ( r2_hidden(k4_tarski('#skF_3'(A_193,B_194,k1_xboole_0),'#skF_5'(A_193,B_194,k1_xboole_0)),A_193)
      | k5_relat_1(A_193,B_194) = k1_xboole_0
      | ~ v1_relat_1(B_194)
      | ~ v1_relat_1(A_193) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_750])).

tff(c_780,plain,(
    ! [B_194] :
      ( k5_relat_1(k1_xboole_0,B_194) = k1_xboole_0
      | ~ v1_relat_1(B_194)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_766,c_81])).

tff(c_792,plain,(
    ! [B_195] :
      ( k5_relat_1(k1_xboole_0,B_195) = k1_xboole_0
      | ~ v1_relat_1(B_195) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_780])).

tff(c_798,plain,(
    k5_relat_1(k1_xboole_0,'#skF_8') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_42,c_792])).

tff(c_804,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_75,c_798])).

tff(c_805,plain,(
    k5_relat_1('#skF_8',k1_xboole_0) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_1207,plain,(
    ! [A_243,B_244,C_245] :
      ( r2_hidden(k4_tarski('#skF_5'(A_243,B_244,C_245),'#skF_4'(A_243,B_244,C_245)),B_244)
      | r2_hidden(k4_tarski('#skF_6'(A_243,B_244,C_245),'#skF_7'(A_243,B_244,C_245)),C_245)
      | k5_relat_1(A_243,B_244) = C_245
      | ~ v1_relat_1(C_245)
      | ~ v1_relat_1(B_244)
      | ~ v1_relat_1(A_243) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_811,plain,(
    ! [A_196,B_197,C_198] :
      ( ~ r1_xboole_0(A_196,B_197)
      | ~ r2_hidden(C_198,k3_xboole_0(A_196,B_197)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_814,plain,(
    ! [A_6,C_198] :
      ( ~ r1_xboole_0(A_6,k1_xboole_0)
      | ~ r2_hidden(C_198,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_811])).

tff(c_816,plain,(
    ! [C_198] : ~ r2_hidden(C_198,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_814])).

tff(c_1237,plain,(
    ! [A_243,B_244] :
      ( r2_hidden(k4_tarski('#skF_5'(A_243,B_244,k1_xboole_0),'#skF_4'(A_243,B_244,k1_xboole_0)),B_244)
      | k5_relat_1(A_243,B_244) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(B_244)
      | ~ v1_relat_1(A_243) ) ),
    inference(resolution,[status(thm)],[c_1207,c_816])).

tff(c_1255,plain,(
    ! [A_246,B_247] :
      ( r2_hidden(k4_tarski('#skF_5'(A_246,B_247,k1_xboole_0),'#skF_4'(A_246,B_247,k1_xboole_0)),B_247)
      | k5_relat_1(A_246,B_247) = k1_xboole_0
      | ~ v1_relat_1(B_247)
      | ~ v1_relat_1(A_246) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_1237])).

tff(c_1269,plain,(
    ! [A_246] :
      ( k5_relat_1(A_246,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_246) ) ),
    inference(resolution,[status(thm)],[c_1255,c_816])).

tff(c_1281,plain,(
    ! [A_248] :
      ( k5_relat_1(A_248,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_248) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_1269])).

tff(c_1287,plain,(
    k5_relat_1('#skF_8',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_42,c_1281])).

tff(c_1292,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_805,c_1287])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 12:33:12 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.37/1.49  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.37/1.49  
% 3.37/1.49  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.37/1.50  %$ r2_hidden > r1_xboole_0 > m1_subset_1 > v1_relat_1 > k5_relat_1 > k4_xboole_0 > k4_tarski > k3_xboole_0 > #nlpp > k1_zfmisc_1 > o_0_0_xboole_0 > k1_xboole_0 > #skF_6 > #skF_2 > #skF_4 > #skF_5 > #skF_7 > #skF_8 > #skF_3 > #skF_1
% 3.37/1.50  
% 3.37/1.50  %Foreground sorts:
% 3.37/1.50  
% 3.37/1.50  
% 3.37/1.50  %Background operators:
% 3.37/1.50  
% 3.37/1.50  
% 3.37/1.50  %Foreground operators:
% 3.37/1.50  tff(o_0_0_xboole_0, type, o_0_0_xboole_0: $i).
% 3.37/1.50  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.37/1.50  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.37/1.50  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 3.37/1.50  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.37/1.50  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i * $i) > $i).
% 3.37/1.50  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.37/1.50  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.37/1.50  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.37/1.50  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 3.37/1.50  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 3.37/1.50  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.37/1.50  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.37/1.50  tff('#skF_7', type, '#skF_7': ($i * $i * $i) > $i).
% 3.37/1.50  tff('#skF_8', type, '#skF_8': $i).
% 3.37/1.50  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.37/1.50  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.37/1.50  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 3.37/1.50  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.37/1.50  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.37/1.50  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.37/1.50  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.37/1.50  
% 3.37/1.51  tff(f_88, negated_conjecture, ~(![A]: (v1_relat_1(A) => ((k5_relat_1(k1_xboole_0, A) = k1_xboole_0) & (k5_relat_1(A, k1_xboole_0) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_relat_1)).
% 3.37/1.51  tff(f_50, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 3.37/1.51  tff(f_63, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.37/1.51  tff(f_81, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => ((C = k5_relat_1(A, B)) <=> (![D, E]: (r2_hidden(k4_tarski(D, E), C) <=> (?[F]: (r2_hidden(k4_tarski(D, F), A) & r2_hidden(k4_tarski(F, E), B)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_relat_1)).
% 3.37/1.51  tff(f_48, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 3.37/1.51  tff(f_42, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 3.37/1.51  tff(f_40, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 3.37/1.51  tff(c_40, plain, (k5_relat_1('#skF_8', k1_xboole_0)!=k1_xboole_0 | k5_relat_1(k1_xboole_0, '#skF_8')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.37/1.51  tff(c_75, plain, (k5_relat_1(k1_xboole_0, '#skF_8')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_40])).
% 3.37/1.51  tff(c_42, plain, (v1_relat_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.37/1.51  tff(c_16, plain, (![A_11]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_11)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.37/1.51  tff(c_65, plain, (![B_121, A_122]: (v1_relat_1(B_121) | ~m1_subset_1(B_121, k1_zfmisc_1(A_122)) | ~v1_relat_1(A_122))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.37/1.51  tff(c_69, plain, (![A_11]: (v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_11))), inference(resolution, [status(thm)], [c_16, c_65])).
% 3.37/1.51  tff(c_70, plain, (![A_11]: (~v1_relat_1(A_11))), inference(splitLeft, [status(thm)], [c_69])).
% 3.37/1.51  tff(c_73, plain, $false, inference(negUnitSimplification, [status(thm)], [c_70, c_42])).
% 3.37/1.51  tff(c_74, plain, (v1_relat_1(k1_xboole_0)), inference(splitRight, [status(thm)], [c_69])).
% 3.37/1.51  tff(c_720, plain, (![A_190, B_191, C_192]: (r2_hidden(k4_tarski('#skF_3'(A_190, B_191, C_192), '#skF_5'(A_190, B_191, C_192)), A_190) | r2_hidden(k4_tarski('#skF_6'(A_190, B_191, C_192), '#skF_7'(A_190, B_191, C_192)), C_192) | k5_relat_1(A_190, B_191)=C_192 | ~v1_relat_1(C_192) | ~v1_relat_1(B_191) | ~v1_relat_1(A_190))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.37/1.51  tff(c_14, plain, (![A_10]: (r1_xboole_0(A_10, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.37/1.51  tff(c_8, plain, (![A_6]: (k3_xboole_0(A_6, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.37/1.51  tff(c_76, plain, (![A_123, B_124, C_125]: (~r1_xboole_0(A_123, B_124) | ~r2_hidden(C_125, k3_xboole_0(A_123, B_124)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.37/1.51  tff(c_79, plain, (![A_6, C_125]: (~r1_xboole_0(A_6, k1_xboole_0) | ~r2_hidden(C_125, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_8, c_76])).
% 3.37/1.51  tff(c_81, plain, (![C_125]: (~r2_hidden(C_125, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_79])).
% 3.37/1.51  tff(c_750, plain, (![A_190, B_191]: (r2_hidden(k4_tarski('#skF_3'(A_190, B_191, k1_xboole_0), '#skF_5'(A_190, B_191, k1_xboole_0)), A_190) | k5_relat_1(A_190, B_191)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(B_191) | ~v1_relat_1(A_190))), inference(resolution, [status(thm)], [c_720, c_81])).
% 3.37/1.51  tff(c_766, plain, (![A_193, B_194]: (r2_hidden(k4_tarski('#skF_3'(A_193, B_194, k1_xboole_0), '#skF_5'(A_193, B_194, k1_xboole_0)), A_193) | k5_relat_1(A_193, B_194)=k1_xboole_0 | ~v1_relat_1(B_194) | ~v1_relat_1(A_193))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_750])).
% 3.37/1.51  tff(c_780, plain, (![B_194]: (k5_relat_1(k1_xboole_0, B_194)=k1_xboole_0 | ~v1_relat_1(B_194) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_766, c_81])).
% 3.37/1.51  tff(c_792, plain, (![B_195]: (k5_relat_1(k1_xboole_0, B_195)=k1_xboole_0 | ~v1_relat_1(B_195))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_780])).
% 3.37/1.51  tff(c_798, plain, (k5_relat_1(k1_xboole_0, '#skF_8')=k1_xboole_0), inference(resolution, [status(thm)], [c_42, c_792])).
% 3.37/1.51  tff(c_804, plain, $false, inference(negUnitSimplification, [status(thm)], [c_75, c_798])).
% 3.37/1.51  tff(c_805, plain, (k5_relat_1('#skF_8', k1_xboole_0)!=k1_xboole_0), inference(splitRight, [status(thm)], [c_40])).
% 3.37/1.51  tff(c_1207, plain, (![A_243, B_244, C_245]: (r2_hidden(k4_tarski('#skF_5'(A_243, B_244, C_245), '#skF_4'(A_243, B_244, C_245)), B_244) | r2_hidden(k4_tarski('#skF_6'(A_243, B_244, C_245), '#skF_7'(A_243, B_244, C_245)), C_245) | k5_relat_1(A_243, B_244)=C_245 | ~v1_relat_1(C_245) | ~v1_relat_1(B_244) | ~v1_relat_1(A_243))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.37/1.51  tff(c_811, plain, (![A_196, B_197, C_198]: (~r1_xboole_0(A_196, B_197) | ~r2_hidden(C_198, k3_xboole_0(A_196, B_197)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.37/1.51  tff(c_814, plain, (![A_6, C_198]: (~r1_xboole_0(A_6, k1_xboole_0) | ~r2_hidden(C_198, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_8, c_811])).
% 3.37/1.51  tff(c_816, plain, (![C_198]: (~r2_hidden(C_198, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_814])).
% 3.37/1.51  tff(c_1237, plain, (![A_243, B_244]: (r2_hidden(k4_tarski('#skF_5'(A_243, B_244, k1_xboole_0), '#skF_4'(A_243, B_244, k1_xboole_0)), B_244) | k5_relat_1(A_243, B_244)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(B_244) | ~v1_relat_1(A_243))), inference(resolution, [status(thm)], [c_1207, c_816])).
% 3.37/1.51  tff(c_1255, plain, (![A_246, B_247]: (r2_hidden(k4_tarski('#skF_5'(A_246, B_247, k1_xboole_0), '#skF_4'(A_246, B_247, k1_xboole_0)), B_247) | k5_relat_1(A_246, B_247)=k1_xboole_0 | ~v1_relat_1(B_247) | ~v1_relat_1(A_246))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_1237])).
% 3.37/1.51  tff(c_1269, plain, (![A_246]: (k5_relat_1(A_246, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_246))), inference(resolution, [status(thm)], [c_1255, c_816])).
% 3.37/1.51  tff(c_1281, plain, (![A_248]: (k5_relat_1(A_248, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_248))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_1269])).
% 3.37/1.51  tff(c_1287, plain, (k5_relat_1('#skF_8', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_42, c_1281])).
% 3.37/1.51  tff(c_1292, plain, $false, inference(negUnitSimplification, [status(thm)], [c_805, c_1287])).
% 3.37/1.51  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.37/1.51  
% 3.37/1.51  Inference rules
% 3.37/1.51  ----------------------
% 3.37/1.51  #Ref     : 0
% 3.37/1.51  #Sup     : 282
% 3.37/1.51  #Fact    : 0
% 3.37/1.51  #Define  : 0
% 3.37/1.51  #Split   : 2
% 3.37/1.51  #Chain   : 0
% 3.37/1.51  #Close   : 0
% 3.37/1.51  
% 3.37/1.51  Ordering : KBO
% 3.37/1.51  
% 3.37/1.51  Simplification rules
% 3.37/1.51  ----------------------
% 3.37/1.51  #Subsume      : 27
% 3.37/1.51  #Demod        : 266
% 3.37/1.51  #Tautology    : 133
% 3.37/1.51  #SimpNegUnit  : 10
% 3.37/1.51  #BackRed      : 1
% 3.37/1.51  
% 3.37/1.51  #Partial instantiations: 0
% 3.37/1.51  #Strategies tried      : 1
% 3.37/1.51  
% 3.37/1.51  Timing (in seconds)
% 3.37/1.51  ----------------------
% 3.37/1.51  Preprocessing        : 0.33
% 3.37/1.51  Parsing              : 0.17
% 3.37/1.51  CNF conversion       : 0.03
% 3.37/1.51  Main loop            : 0.43
% 3.37/1.51  Inferencing          : 0.16
% 3.37/1.51  Reduction            : 0.15
% 3.37/1.51  Demodulation         : 0.11
% 3.37/1.51  BG Simplification    : 0.02
% 3.37/1.51  Subsumption          : 0.07
% 3.37/1.51  Abstraction          : 0.03
% 3.37/1.51  MUC search           : 0.00
% 3.37/1.51  Cooper               : 0.00
% 3.37/1.51  Total                : 0.79
% 3.37/1.51  Index Insertion      : 0.00
% 3.37/1.51  Index Deletion       : 0.00
% 3.37/1.51  Index Matching       : 0.00
% 3.37/1.51  BG Taut test         : 0.00
%------------------------------------------------------------------------------
