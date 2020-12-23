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
% DateTime   : Thu Dec  3 09:58:24 EST 2020

% Result     : Theorem 3.53s
% Output     : CNFRefutation 3.53s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 135 expanded)
%              Number of leaves         :   35 (  58 expanded)
%              Depth                    :   11
%              Number of atoms          :  118 ( 216 expanded)
%              Number of equality atoms :   19 (  36 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_3 > #skF_5 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_94,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_72,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_76,axiom,(
    ! [A,B,C] : r1_tarski(k2_xboole_0(k3_xboole_0(A,B),k3_xboole_0(A,C)),k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_xboole_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_82,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_84,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

tff(f_64,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_102,axiom,(
    ! [A,B,C,D] :
      ( ( k2_xboole_0(A,B) = k2_xboole_0(C,D)
        & r1_xboole_0(C,A)
        & r1_xboole_0(D,B) )
     => C = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_xboole_1)).

tff(f_146,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => r1_tarski(k2_relat_1(k3_xboole_0(A,B)),k3_xboole_0(k2_relat_1(A),k2_relat_1(B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_relat_1)).

tff(f_123,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k4_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_relat_1)).

tff(f_138,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(A,B)
           => ( r1_tarski(k1_relat_1(A),k1_relat_1(B))
              & r1_tarski(k2_relat_1(A),k2_relat_1(B)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).

tff(f_78,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C) )
     => r1_tarski(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).

tff(c_38,plain,(
    ! [A_38] : r1_xboole_0(A_38,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_20,plain,(
    ! [A_19] : k2_xboole_0(A_19,k1_xboole_0) = A_19 ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_551,plain,(
    ! [A_149,B_150,C_151] : r1_tarski(k2_xboole_0(k3_xboole_0(A_149,B_150),k3_xboole_0(A_149,C_151)),k2_xboole_0(B_150,C_151)) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_565,plain,(
    ! [A_149,A_19] : r1_tarski(k2_xboole_0(k3_xboole_0(A_149,A_19),k3_xboole_0(A_149,k1_xboole_0)),A_19) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_551])).

tff(c_10,plain,(
    ! [A_6,B_7] :
      ( r2_hidden('#skF_2'(A_6,B_7),B_7)
      | r1_xboole_0(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_246,plain,(
    ! [C_107,B_108,A_109] :
      ( r2_hidden(C_107,B_108)
      | ~ r2_hidden(C_107,A_109)
      | ~ r1_tarski(A_109,B_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_648,plain,(
    ! [A_168,B_169,B_170] :
      ( r2_hidden('#skF_2'(A_168,B_169),B_170)
      | ~ r1_tarski(B_169,B_170)
      | r1_xboole_0(A_168,B_169) ) ),
    inference(resolution,[status(thm)],[c_10,c_246])).

tff(c_100,plain,(
    ! [A_69,B_70] : k4_xboole_0(A_69,k4_xboole_0(A_69,B_70)) = k3_xboole_0(A_69,B_70) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_32,plain,(
    ! [A_31] : k4_xboole_0(k1_xboole_0,A_31) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_116,plain,(
    ! [B_70] : k3_xboole_0(k1_xboole_0,B_70) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_100,c_32])).

tff(c_163,plain,(
    ! [A_84,B_85,C_86] :
      ( ~ r1_xboole_0(A_84,B_85)
      | ~ r2_hidden(C_86,k3_xboole_0(A_84,B_85)) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_174,plain,(
    ! [B_70,C_86] :
      ( ~ r1_xboole_0(k1_xboole_0,B_70)
      | ~ r2_hidden(C_86,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_116,c_163])).

tff(c_177,plain,(
    ! [C_86] : ~ r2_hidden(C_86,k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_174])).

tff(c_670,plain,(
    ! [B_169,A_168] :
      ( ~ r1_tarski(B_169,k1_xboole_0)
      | r1_xboole_0(A_168,B_169) ) ),
    inference(resolution,[status(thm)],[c_648,c_177])).

tff(c_1301,plain,(
    ! [C_243,B_244,D_245,A_246] :
      ( C_243 = B_244
      | ~ r1_xboole_0(D_245,B_244)
      | ~ r1_xboole_0(C_243,A_246)
      | k2_xboole_0(C_243,D_245) != k2_xboole_0(A_246,B_244) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_1327,plain,(
    ! [C_243,A_246,A_38] :
      ( k1_xboole_0 = C_243
      | ~ r1_xboole_0(C_243,A_246)
      | k2_xboole_0(C_243,A_38) != k2_xboole_0(A_246,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_38,c_1301])).

tff(c_1344,plain,(
    ! [C_247,A_248,A_249] :
      ( k1_xboole_0 = C_247
      | ~ r1_xboole_0(C_247,A_248)
      | k2_xboole_0(C_247,A_249) != A_248 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_1327])).

tff(c_1372,plain,(
    ! [A_168,A_249,B_169] :
      ( k1_xboole_0 = A_168
      | k2_xboole_0(A_168,A_249) != B_169
      | ~ r1_tarski(B_169,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_670,c_1344])).

tff(c_1600,plain,(
    ! [A_267,A_268] :
      ( k1_xboole_0 = A_267
      | ~ r1_tarski(k2_xboole_0(A_267,A_268),k1_xboole_0) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_1372])).

tff(c_1619,plain,(
    ! [A_149] : k3_xboole_0(A_149,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_565,c_1600])).

tff(c_1639,plain,(
    ! [A_149,A_19] : r1_tarski(k2_xboole_0(k3_xboole_0(A_149,A_19),k1_xboole_0),A_19) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1619,c_565])).

tff(c_1642,plain,(
    ! [A_149,A_19] : r1_tarski(k3_xboole_0(A_149,A_19),A_19) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_1639])).

tff(c_62,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_50,plain,(
    ! [A_51,B_52] :
      ( v1_relat_1(k4_xboole_0(A_51,B_52))
      | ~ v1_relat_1(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_109,plain,(
    ! [A_69,B_70] :
      ( v1_relat_1(k3_xboole_0(A_69,B_70))
      | ~ v1_relat_1(A_69) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_100,c_50])).

tff(c_60,plain,(
    v1_relat_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_1215,plain,(
    ! [A_235,B_236] :
      ( r1_tarski(k2_relat_1(A_235),k2_relat_1(B_236))
      | ~ r1_tarski(A_235,B_236)
      | ~ v1_relat_1(B_236)
      | ~ v1_relat_1(A_235) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_26,plain,(
    ! [A_24,B_25] : r1_tarski(k4_xboole_0(A_24,B_25),A_24) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_112,plain,(
    ! [A_69,B_70] : r1_tarski(k3_xboole_0(A_69,B_70),A_69) ),
    inference(superposition,[status(thm),theory(equality)],[c_100,c_26])).

tff(c_1022,plain,(
    ! [A_213,B_214] :
      ( r1_tarski(k2_relat_1(A_213),k2_relat_1(B_214))
      | ~ r1_tarski(A_213,B_214)
      | ~ v1_relat_1(B_214)
      | ~ v1_relat_1(A_213) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_637,plain,(
    ! [A_165,B_166,C_167] :
      ( r1_tarski(A_165,k3_xboole_0(B_166,C_167))
      | ~ r1_tarski(A_165,C_167)
      | ~ r1_tarski(A_165,B_166) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_58,plain,(
    ~ r1_tarski(k2_relat_1(k3_xboole_0('#skF_4','#skF_5')),k3_xboole_0(k2_relat_1('#skF_4'),k2_relat_1('#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_647,plain,
    ( ~ r1_tarski(k2_relat_1(k3_xboole_0('#skF_4','#skF_5')),k2_relat_1('#skF_5'))
    | ~ r1_tarski(k2_relat_1(k3_xboole_0('#skF_4','#skF_5')),k2_relat_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_637,c_58])).

tff(c_696,plain,(
    ~ r1_tarski(k2_relat_1(k3_xboole_0('#skF_4','#skF_5')),k2_relat_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_647])).

tff(c_1025,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_4','#skF_5'),'#skF_4')
    | ~ v1_relat_1('#skF_4')
    | ~ v1_relat_1(k3_xboole_0('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_1022,c_696])).

tff(c_1030,plain,(
    ~ v1_relat_1(k3_xboole_0('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_112,c_1025])).

tff(c_1034,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_109,c_1030])).

tff(c_1038,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_1034])).

tff(c_1039,plain,(
    ~ r1_tarski(k2_relat_1(k3_xboole_0('#skF_4','#skF_5')),k2_relat_1('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_647])).

tff(c_1218,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_4','#skF_5'),'#skF_5')
    | ~ v1_relat_1('#skF_5')
    | ~ v1_relat_1(k3_xboole_0('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_1215,c_1039])).

tff(c_1223,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_4','#skF_5'),'#skF_5')
    | ~ v1_relat_1(k3_xboole_0('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_1218])).

tff(c_1225,plain,(
    ~ v1_relat_1(k3_xboole_0('#skF_4','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_1223])).

tff(c_1228,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_109,c_1225])).

tff(c_1232,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_1228])).

tff(c_1233,plain,(
    ~ r1_tarski(k3_xboole_0('#skF_4','#skF_5'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_1223])).

tff(c_1784,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1642,c_1233])).

tff(c_1786,plain,(
    ! [B_276] : ~ r1_xboole_0(k1_xboole_0,B_276) ),
    inference(splitRight,[status(thm)],[c_174])).

tff(c_1791,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_38,c_1786])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n006.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 10:03:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.53/1.61  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.53/1.62  
% 3.53/1.62  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.53/1.62  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_3 > #skF_5 > #skF_4 > #skF_2 > #skF_1
% 3.53/1.62  
% 3.53/1.62  %Foreground sorts:
% 3.53/1.62  
% 3.53/1.62  
% 3.53/1.62  %Background operators:
% 3.53/1.62  
% 3.53/1.62  
% 3.53/1.62  %Foreground operators:
% 3.53/1.62  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.53/1.62  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.53/1.62  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.53/1.62  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.53/1.62  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.53/1.62  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.53/1.62  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.53/1.62  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.53/1.62  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.53/1.62  tff('#skF_5', type, '#skF_5': $i).
% 3.53/1.62  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.53/1.62  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.53/1.62  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.53/1.62  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.53/1.62  tff('#skF_4', type, '#skF_4': $i).
% 3.53/1.62  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.53/1.62  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.53/1.62  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.53/1.62  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.53/1.62  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.53/1.62  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.53/1.62  
% 3.53/1.64  tff(f_94, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 3.53/1.64  tff(f_72, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 3.53/1.64  tff(f_76, axiom, (![A, B, C]: r1_tarski(k2_xboole_0(k3_xboole_0(A, B), k3_xboole_0(A, C)), k2_xboole_0(B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_xboole_1)).
% 3.53/1.64  tff(f_50, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 3.53/1.64  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 3.53/1.64  tff(f_82, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 3.53/1.64  tff(f_84, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_boole)).
% 3.53/1.64  tff(f_64, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 3.53/1.64  tff(f_102, axiom, (![A, B, C, D]: ((((k2_xboole_0(A, B) = k2_xboole_0(C, D)) & r1_xboole_0(C, A)) & r1_xboole_0(D, B)) => (C = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_xboole_1)).
% 3.53/1.64  tff(f_146, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k3_xboole_0(A, B)), k3_xboole_0(k2_relat_1(A), k2_relat_1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t27_relat_1)).
% 3.53/1.64  tff(f_123, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_relat_1)).
% 3.53/1.64  tff(f_138, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => (r1_tarski(k1_relat_1(A), k1_relat_1(B)) & r1_tarski(k2_relat_1(A), k2_relat_1(B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_relat_1)).
% 3.53/1.64  tff(f_78, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 3.53/1.64  tff(f_70, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(A, C)) => r1_tarski(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_xboole_1)).
% 3.53/1.64  tff(c_38, plain, (![A_38]: (r1_xboole_0(A_38, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.53/1.64  tff(c_20, plain, (![A_19]: (k2_xboole_0(A_19, k1_xboole_0)=A_19)), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.53/1.64  tff(c_551, plain, (![A_149, B_150, C_151]: (r1_tarski(k2_xboole_0(k3_xboole_0(A_149, B_150), k3_xboole_0(A_149, C_151)), k2_xboole_0(B_150, C_151)))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.53/1.64  tff(c_565, plain, (![A_149, A_19]: (r1_tarski(k2_xboole_0(k3_xboole_0(A_149, A_19), k3_xboole_0(A_149, k1_xboole_0)), A_19))), inference(superposition, [status(thm), theory('equality')], [c_20, c_551])).
% 3.53/1.64  tff(c_10, plain, (![A_6, B_7]: (r2_hidden('#skF_2'(A_6, B_7), B_7) | r1_xboole_0(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.53/1.64  tff(c_246, plain, (![C_107, B_108, A_109]: (r2_hidden(C_107, B_108) | ~r2_hidden(C_107, A_109) | ~r1_tarski(A_109, B_108))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.53/1.64  tff(c_648, plain, (![A_168, B_169, B_170]: (r2_hidden('#skF_2'(A_168, B_169), B_170) | ~r1_tarski(B_169, B_170) | r1_xboole_0(A_168, B_169))), inference(resolution, [status(thm)], [c_10, c_246])).
% 3.53/1.64  tff(c_100, plain, (![A_69, B_70]: (k4_xboole_0(A_69, k4_xboole_0(A_69, B_70))=k3_xboole_0(A_69, B_70))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.53/1.64  tff(c_32, plain, (![A_31]: (k4_xboole_0(k1_xboole_0, A_31)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.53/1.64  tff(c_116, plain, (![B_70]: (k3_xboole_0(k1_xboole_0, B_70)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_100, c_32])).
% 3.53/1.64  tff(c_163, plain, (![A_84, B_85, C_86]: (~r1_xboole_0(A_84, B_85) | ~r2_hidden(C_86, k3_xboole_0(A_84, B_85)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.53/1.64  tff(c_174, plain, (![B_70, C_86]: (~r1_xboole_0(k1_xboole_0, B_70) | ~r2_hidden(C_86, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_116, c_163])).
% 3.53/1.64  tff(c_177, plain, (![C_86]: (~r2_hidden(C_86, k1_xboole_0))), inference(splitLeft, [status(thm)], [c_174])).
% 3.53/1.64  tff(c_670, plain, (![B_169, A_168]: (~r1_tarski(B_169, k1_xboole_0) | r1_xboole_0(A_168, B_169))), inference(resolution, [status(thm)], [c_648, c_177])).
% 3.53/1.64  tff(c_1301, plain, (![C_243, B_244, D_245, A_246]: (C_243=B_244 | ~r1_xboole_0(D_245, B_244) | ~r1_xboole_0(C_243, A_246) | k2_xboole_0(C_243, D_245)!=k2_xboole_0(A_246, B_244))), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.53/1.64  tff(c_1327, plain, (![C_243, A_246, A_38]: (k1_xboole_0=C_243 | ~r1_xboole_0(C_243, A_246) | k2_xboole_0(C_243, A_38)!=k2_xboole_0(A_246, k1_xboole_0))), inference(resolution, [status(thm)], [c_38, c_1301])).
% 3.53/1.64  tff(c_1344, plain, (![C_247, A_248, A_249]: (k1_xboole_0=C_247 | ~r1_xboole_0(C_247, A_248) | k2_xboole_0(C_247, A_249)!=A_248)), inference(demodulation, [status(thm), theory('equality')], [c_20, c_1327])).
% 3.53/1.64  tff(c_1372, plain, (![A_168, A_249, B_169]: (k1_xboole_0=A_168 | k2_xboole_0(A_168, A_249)!=B_169 | ~r1_tarski(B_169, k1_xboole_0))), inference(resolution, [status(thm)], [c_670, c_1344])).
% 3.53/1.64  tff(c_1600, plain, (![A_267, A_268]: (k1_xboole_0=A_267 | ~r1_tarski(k2_xboole_0(A_267, A_268), k1_xboole_0))), inference(reflexivity, [status(thm), theory('equality')], [c_1372])).
% 3.53/1.64  tff(c_1619, plain, (![A_149]: (k3_xboole_0(A_149, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_565, c_1600])).
% 3.53/1.64  tff(c_1639, plain, (![A_149, A_19]: (r1_tarski(k2_xboole_0(k3_xboole_0(A_149, A_19), k1_xboole_0), A_19))), inference(demodulation, [status(thm), theory('equality')], [c_1619, c_565])).
% 3.53/1.64  tff(c_1642, plain, (![A_149, A_19]: (r1_tarski(k3_xboole_0(A_149, A_19), A_19))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_1639])).
% 3.53/1.64  tff(c_62, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_146])).
% 3.53/1.64  tff(c_50, plain, (![A_51, B_52]: (v1_relat_1(k4_xboole_0(A_51, B_52)) | ~v1_relat_1(A_51))), inference(cnfTransformation, [status(thm)], [f_123])).
% 3.53/1.64  tff(c_109, plain, (![A_69, B_70]: (v1_relat_1(k3_xboole_0(A_69, B_70)) | ~v1_relat_1(A_69))), inference(superposition, [status(thm), theory('equality')], [c_100, c_50])).
% 3.53/1.64  tff(c_60, plain, (v1_relat_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_146])).
% 3.53/1.64  tff(c_1215, plain, (![A_235, B_236]: (r1_tarski(k2_relat_1(A_235), k2_relat_1(B_236)) | ~r1_tarski(A_235, B_236) | ~v1_relat_1(B_236) | ~v1_relat_1(A_235))), inference(cnfTransformation, [status(thm)], [f_138])).
% 3.53/1.64  tff(c_26, plain, (![A_24, B_25]: (r1_tarski(k4_xboole_0(A_24, B_25), A_24))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.53/1.64  tff(c_112, plain, (![A_69, B_70]: (r1_tarski(k3_xboole_0(A_69, B_70), A_69))), inference(superposition, [status(thm), theory('equality')], [c_100, c_26])).
% 3.53/1.64  tff(c_1022, plain, (![A_213, B_214]: (r1_tarski(k2_relat_1(A_213), k2_relat_1(B_214)) | ~r1_tarski(A_213, B_214) | ~v1_relat_1(B_214) | ~v1_relat_1(A_213))), inference(cnfTransformation, [status(thm)], [f_138])).
% 3.53/1.64  tff(c_637, plain, (![A_165, B_166, C_167]: (r1_tarski(A_165, k3_xboole_0(B_166, C_167)) | ~r1_tarski(A_165, C_167) | ~r1_tarski(A_165, B_166))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.53/1.64  tff(c_58, plain, (~r1_tarski(k2_relat_1(k3_xboole_0('#skF_4', '#skF_5')), k3_xboole_0(k2_relat_1('#skF_4'), k2_relat_1('#skF_5')))), inference(cnfTransformation, [status(thm)], [f_146])).
% 3.53/1.64  tff(c_647, plain, (~r1_tarski(k2_relat_1(k3_xboole_0('#skF_4', '#skF_5')), k2_relat_1('#skF_5')) | ~r1_tarski(k2_relat_1(k3_xboole_0('#skF_4', '#skF_5')), k2_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_637, c_58])).
% 3.53/1.64  tff(c_696, plain, (~r1_tarski(k2_relat_1(k3_xboole_0('#skF_4', '#skF_5')), k2_relat_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_647])).
% 3.53/1.64  tff(c_1025, plain, (~r1_tarski(k3_xboole_0('#skF_4', '#skF_5'), '#skF_4') | ~v1_relat_1('#skF_4') | ~v1_relat_1(k3_xboole_0('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_1022, c_696])).
% 3.53/1.64  tff(c_1030, plain, (~v1_relat_1(k3_xboole_0('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_112, c_1025])).
% 3.53/1.64  tff(c_1034, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_109, c_1030])).
% 3.53/1.64  tff(c_1038, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_62, c_1034])).
% 3.53/1.64  tff(c_1039, plain, (~r1_tarski(k2_relat_1(k3_xboole_0('#skF_4', '#skF_5')), k2_relat_1('#skF_5'))), inference(splitRight, [status(thm)], [c_647])).
% 3.53/1.64  tff(c_1218, plain, (~r1_tarski(k3_xboole_0('#skF_4', '#skF_5'), '#skF_5') | ~v1_relat_1('#skF_5') | ~v1_relat_1(k3_xboole_0('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_1215, c_1039])).
% 3.53/1.64  tff(c_1223, plain, (~r1_tarski(k3_xboole_0('#skF_4', '#skF_5'), '#skF_5') | ~v1_relat_1(k3_xboole_0('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_1218])).
% 3.53/1.64  tff(c_1225, plain, (~v1_relat_1(k3_xboole_0('#skF_4', '#skF_5'))), inference(splitLeft, [status(thm)], [c_1223])).
% 3.53/1.64  tff(c_1228, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_109, c_1225])).
% 3.53/1.64  tff(c_1232, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_62, c_1228])).
% 3.53/1.64  tff(c_1233, plain, (~r1_tarski(k3_xboole_0('#skF_4', '#skF_5'), '#skF_5')), inference(splitRight, [status(thm)], [c_1223])).
% 3.53/1.64  tff(c_1784, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1642, c_1233])).
% 3.53/1.64  tff(c_1786, plain, (![B_276]: (~r1_xboole_0(k1_xboole_0, B_276))), inference(splitRight, [status(thm)], [c_174])).
% 3.53/1.64  tff(c_1791, plain, $false, inference(resolution, [status(thm)], [c_38, c_1786])).
% 3.53/1.64  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.53/1.64  
% 3.53/1.64  Inference rules
% 3.53/1.64  ----------------------
% 3.53/1.64  #Ref     : 1
% 3.53/1.64  #Sup     : 412
% 3.53/1.64  #Fact    : 0
% 3.53/1.64  #Define  : 0
% 3.53/1.64  #Split   : 5
% 3.53/1.64  #Chain   : 0
% 3.53/1.64  #Close   : 0
% 3.53/1.64  
% 3.53/1.64  Ordering : KBO
% 3.53/1.64  
% 3.53/1.64  Simplification rules
% 3.53/1.64  ----------------------
% 3.53/1.64  #Subsume      : 42
% 3.53/1.64  #Demod        : 236
% 3.53/1.64  #Tautology    : 146
% 3.53/1.64  #SimpNegUnit  : 9
% 3.53/1.64  #BackRed      : 8
% 3.53/1.64  
% 3.53/1.64  #Partial instantiations: 0
% 3.53/1.64  #Strategies tried      : 1
% 3.53/1.64  
% 3.53/1.64  Timing (in seconds)
% 3.53/1.64  ----------------------
% 3.86/1.64  Preprocessing        : 0.34
% 3.86/1.64  Parsing              : 0.18
% 3.86/1.64  CNF conversion       : 0.03
% 3.86/1.64  Main loop            : 0.53
% 3.86/1.64  Inferencing          : 0.19
% 3.86/1.64  Reduction            : 0.17
% 3.86/1.64  Demodulation         : 0.12
% 3.86/1.64  BG Simplification    : 0.03
% 3.86/1.64  Subsumption          : 0.09
% 3.86/1.64  Abstraction          : 0.03
% 3.86/1.64  MUC search           : 0.00
% 3.86/1.64  Cooper               : 0.00
% 3.86/1.64  Total                : 0.90
% 3.86/1.64  Index Insertion      : 0.00
% 3.86/1.64  Index Deletion       : 0.00
% 3.86/1.64  Index Matching       : 0.00
% 3.86/1.64  BG Taut test         : 0.00
%------------------------------------------------------------------------------
