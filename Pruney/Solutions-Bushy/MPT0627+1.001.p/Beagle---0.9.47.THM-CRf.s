%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0627+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:36:36 EST 2020

% Result     : Theorem 11.00s
% Output     : CNFRefutation 11.00s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 291 expanded)
%              Number of leaves         :   30 ( 115 expanded)
%              Depth                    :   15
%              Number of atoms          :  147 ( 949 expanded)
%              Number of equality atoms :   18 ( 190 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > v1_funct_1 > k5_relat_1 > k4_tarski > k1_funct_1 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_11 > #skF_6 > #skF_4 > #skF_5 > #skF_3 > #skF_13 > #skF_7 > #skF_9 > #skF_2 > #skF_8 > #skF_1 > #skF_12 > #skF_10

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff('#skF_13',type,(
    '#skF_13': $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i ) > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_12',type,(
    '#skF_12': $i )).

tff('#skF_10',type,(
    '#skF_10': ( $i * $i * $i ) > $i )).

tff(f_100,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => ! [C] :
            ( ( v1_relat_1(C)
              & v1_funct_1(C) )
           => ( r2_hidden(A,k1_relat_1(k5_relat_1(C,B)))
             => k1_funct_1(k5_relat_1(C,B),A) = k1_funct_1(B,k1_funct_1(C,A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_funct_1)).

tff(f_74,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k5_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

tff(f_42,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B,C] :
          ( ( r2_hidden(B,k1_relat_1(A))
           => ( C = k1_funct_1(A,B)
            <=> r2_hidden(k4_tarski(B,C),A) ) )
          & ( ~ r2_hidden(B,k1_relat_1(A))
           => ( C = k1_funct_1(A,B)
            <=> C = k1_xboole_0 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_funct_1)).

tff(f_86,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A)
        & v1_relat_1(B)
        & v1_funct_1(B) )
     => ( v1_relat_1(k5_relat_1(A,B))
        & v1_funct_1(k5_relat_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_funct_1)).

tff(f_68,axiom,(
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

tff(c_46,plain,(
    k1_funct_1(k5_relat_1('#skF_13','#skF_12'),'#skF_11') != k1_funct_1('#skF_12',k1_funct_1('#skF_13','#skF_11')) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_56,plain,(
    v1_relat_1('#skF_12') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_54,plain,(
    v1_funct_1('#skF_12') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_52,plain,(
    v1_relat_1('#skF_13') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_40,plain,(
    ! [A_124,B_125] :
      ( v1_relat_1(k5_relat_1(A_124,B_125))
      | ~ v1_relat_1(B_125)
      | ~ v1_relat_1(A_124) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_48,plain,(
    r2_hidden('#skF_11',k1_relat_1(k5_relat_1('#skF_13','#skF_12'))) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_10,plain,(
    ! [C_21,A_6] :
      ( r2_hidden(k4_tarski(C_21,'#skF_4'(A_6,k1_relat_1(A_6),C_21)),A_6)
      | ~ r2_hidden(C_21,k1_relat_1(A_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_110,plain,(
    ! [A_154,B_155,C_156] :
      ( k1_funct_1(A_154,B_155) = C_156
      | ~ r2_hidden(k4_tarski(B_155,C_156),A_154)
      | ~ r2_hidden(B_155,k1_relat_1(A_154))
      | ~ v1_funct_1(A_154)
      | ~ v1_relat_1(A_154) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_134,plain,(
    ! [A_157,C_158] :
      ( '#skF_4'(A_157,k1_relat_1(A_157),C_158) = k1_funct_1(A_157,C_158)
      | ~ v1_funct_1(A_157)
      | ~ v1_relat_1(A_157)
      | ~ r2_hidden(C_158,k1_relat_1(A_157)) ) ),
    inference(resolution,[status(thm)],[c_10,c_110])).

tff(c_166,plain,
    ( '#skF_4'(k5_relat_1('#skF_13','#skF_12'),k1_relat_1(k5_relat_1('#skF_13','#skF_12')),'#skF_11') = k1_funct_1(k5_relat_1('#skF_13','#skF_12'),'#skF_11')
    | ~ v1_funct_1(k5_relat_1('#skF_13','#skF_12'))
    | ~ v1_relat_1(k5_relat_1('#skF_13','#skF_12')) ),
    inference(resolution,[status(thm)],[c_48,c_134])).

tff(c_167,plain,(
    ~ v1_relat_1(k5_relat_1('#skF_13','#skF_12')) ),
    inference(splitLeft,[status(thm)],[c_166])).

tff(c_170,plain,
    ( ~ v1_relat_1('#skF_12')
    | ~ v1_relat_1('#skF_13') ),
    inference(resolution,[status(thm)],[c_40,c_167])).

tff(c_174,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_56,c_170])).

tff(c_176,plain,(
    v1_relat_1(k5_relat_1('#skF_13','#skF_12')) ),
    inference(splitRight,[status(thm)],[c_166])).

tff(c_50,plain,(
    v1_funct_1('#skF_13') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_42,plain,(
    ! [A_126,B_127] :
      ( v1_funct_1(k5_relat_1(A_126,B_127))
      | ~ v1_funct_1(B_127)
      | ~ v1_relat_1(B_127)
      | ~ v1_funct_1(A_126)
      | ~ v1_relat_1(A_126) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_175,plain,
    ( ~ v1_funct_1(k5_relat_1('#skF_13','#skF_12'))
    | '#skF_4'(k5_relat_1('#skF_13','#skF_12'),k1_relat_1(k5_relat_1('#skF_13','#skF_12')),'#skF_11') = k1_funct_1(k5_relat_1('#skF_13','#skF_12'),'#skF_11') ),
    inference(splitRight,[status(thm)],[c_166])).

tff(c_227,plain,(
    ~ v1_funct_1(k5_relat_1('#skF_13','#skF_12')) ),
    inference(splitLeft,[status(thm)],[c_175])).

tff(c_251,plain,
    ( ~ v1_funct_1('#skF_12')
    | ~ v1_relat_1('#skF_12')
    | ~ v1_funct_1('#skF_13')
    | ~ v1_relat_1('#skF_13') ),
    inference(resolution,[status(thm)],[c_42,c_227])).

tff(c_255,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_56,c_54,c_251])).

tff(c_256,plain,(
    '#skF_4'(k5_relat_1('#skF_13','#skF_12'),k1_relat_1(k5_relat_1('#skF_13','#skF_12')),'#skF_11') = k1_funct_1(k5_relat_1('#skF_13','#skF_12'),'#skF_11') ),
    inference(splitRight,[status(thm)],[c_175])).

tff(c_264,plain,
    ( r2_hidden(k4_tarski('#skF_11',k1_funct_1(k5_relat_1('#skF_13','#skF_12'),'#skF_11')),k5_relat_1('#skF_13','#skF_12'))
    | ~ r2_hidden('#skF_11',k1_relat_1(k5_relat_1('#skF_13','#skF_12'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_256,c_10])).

tff(c_274,plain,(
    r2_hidden(k4_tarski('#skF_11',k1_funct_1(k5_relat_1('#skF_13','#skF_12'),'#skF_11')),k5_relat_1('#skF_13','#skF_12')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_264])).

tff(c_978,plain,(
    ! [D_232,B_233,A_234,E_235] :
      ( r2_hidden(k4_tarski(D_232,'#skF_5'(D_232,B_233,A_234,E_235,k5_relat_1(A_234,B_233))),A_234)
      | ~ r2_hidden(k4_tarski(D_232,E_235),k5_relat_1(A_234,B_233))
      | ~ v1_relat_1(k5_relat_1(A_234,B_233))
      | ~ v1_relat_1(B_233)
      | ~ v1_relat_1(A_234) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_12,plain,(
    ! [C_21,A_6,D_24] :
      ( r2_hidden(C_21,k1_relat_1(A_6))
      | ~ r2_hidden(k4_tarski(C_21,D_24),A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_1011,plain,(
    ! [D_236,A_237,E_238,B_239] :
      ( r2_hidden(D_236,k1_relat_1(A_237))
      | ~ r2_hidden(k4_tarski(D_236,E_238),k5_relat_1(A_237,B_239))
      | ~ v1_relat_1(k5_relat_1(A_237,B_239))
      | ~ v1_relat_1(B_239)
      | ~ v1_relat_1(A_237) ) ),
    inference(resolution,[status(thm)],[c_978,c_12])).

tff(c_1029,plain,
    ( r2_hidden('#skF_11',k1_relat_1('#skF_13'))
    | ~ v1_relat_1(k5_relat_1('#skF_13','#skF_12'))
    | ~ v1_relat_1('#skF_12')
    | ~ v1_relat_1('#skF_13') ),
    inference(resolution,[status(thm)],[c_274,c_1011])).

tff(c_1050,plain,(
    r2_hidden('#skF_11',k1_relat_1('#skF_13')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_56,c_176,c_1029])).

tff(c_2,plain,(
    ! [A_1,B_4,C_5] :
      ( k1_funct_1(A_1,B_4) = C_5
      | ~ r2_hidden(k4_tarski(B_4,C_5),A_1)
      | ~ r2_hidden(B_4,k1_relat_1(A_1))
      | ~ v1_funct_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_14883,plain,(
    ! [D_502,B_503,A_504,E_505] :
      ( '#skF_5'(D_502,B_503,A_504,E_505,k5_relat_1(A_504,B_503)) = k1_funct_1(A_504,D_502)
      | ~ r2_hidden(D_502,k1_relat_1(A_504))
      | ~ v1_funct_1(A_504)
      | ~ r2_hidden(k4_tarski(D_502,E_505),k5_relat_1(A_504,B_503))
      | ~ v1_relat_1(k5_relat_1(A_504,B_503))
      | ~ v1_relat_1(B_503)
      | ~ v1_relat_1(A_504) ) ),
    inference(resolution,[status(thm)],[c_978,c_2])).

tff(c_14943,plain,
    ( '#skF_5'('#skF_11','#skF_12','#skF_13',k1_funct_1(k5_relat_1('#skF_13','#skF_12'),'#skF_11'),k5_relat_1('#skF_13','#skF_12')) = k1_funct_1('#skF_13','#skF_11')
    | ~ r2_hidden('#skF_11',k1_relat_1('#skF_13'))
    | ~ v1_funct_1('#skF_13')
    | ~ v1_relat_1(k5_relat_1('#skF_13','#skF_12'))
    | ~ v1_relat_1('#skF_12')
    | ~ v1_relat_1('#skF_13') ),
    inference(resolution,[status(thm)],[c_274,c_14883])).

tff(c_14996,plain,(
    '#skF_5'('#skF_11','#skF_12','#skF_13',k1_funct_1(k5_relat_1('#skF_13','#skF_12'),'#skF_11'),k5_relat_1('#skF_13','#skF_12')) = k1_funct_1('#skF_13','#skF_11') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_56,c_176,c_50,c_1050,c_14943])).

tff(c_729,plain,(
    ! [D_210,B_211,A_212,E_213] :
      ( r2_hidden(k4_tarski('#skF_5'(D_210,B_211,A_212,E_213,k5_relat_1(A_212,B_211)),E_213),B_211)
      | ~ r2_hidden(k4_tarski(D_210,E_213),k5_relat_1(A_212,B_211))
      | ~ v1_relat_1(k5_relat_1(A_212,B_211))
      | ~ v1_relat_1(B_211)
      | ~ v1_relat_1(A_212) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_744,plain,(
    ! [D_210,B_211,A_212,E_213] :
      ( r2_hidden('#skF_5'(D_210,B_211,A_212,E_213,k5_relat_1(A_212,B_211)),k1_relat_1(B_211))
      | ~ r2_hidden(k4_tarski(D_210,E_213),k5_relat_1(A_212,B_211))
      | ~ v1_relat_1(k5_relat_1(A_212,B_211))
      | ~ v1_relat_1(B_211)
      | ~ v1_relat_1(A_212) ) ),
    inference(resolution,[status(thm)],[c_729,c_12])).

tff(c_15006,plain,
    ( r2_hidden(k1_funct_1('#skF_13','#skF_11'),k1_relat_1('#skF_12'))
    | ~ r2_hidden(k4_tarski('#skF_11',k1_funct_1(k5_relat_1('#skF_13','#skF_12'),'#skF_11')),k5_relat_1('#skF_13','#skF_12'))
    | ~ v1_relat_1(k5_relat_1('#skF_13','#skF_12'))
    | ~ v1_relat_1('#skF_12')
    | ~ v1_relat_1('#skF_13') ),
    inference(superposition,[status(thm),theory(equality)],[c_14996,c_744])).

tff(c_15022,plain,(
    r2_hidden(k1_funct_1('#skF_13','#skF_11'),k1_relat_1('#skF_12')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_56,c_176,c_274,c_15006])).

tff(c_36,plain,(
    ! [D_116,B_77,A_25,E_117] :
      ( r2_hidden(k4_tarski('#skF_5'(D_116,B_77,A_25,E_117,k5_relat_1(A_25,B_77)),E_117),B_77)
      | ~ r2_hidden(k4_tarski(D_116,E_117),k5_relat_1(A_25,B_77))
      | ~ v1_relat_1(k5_relat_1(A_25,B_77))
      | ~ v1_relat_1(B_77)
      | ~ v1_relat_1(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_15009,plain,
    ( r2_hidden(k4_tarski(k1_funct_1('#skF_13','#skF_11'),k1_funct_1(k5_relat_1('#skF_13','#skF_12'),'#skF_11')),'#skF_12')
    | ~ r2_hidden(k4_tarski('#skF_11',k1_funct_1(k5_relat_1('#skF_13','#skF_12'),'#skF_11')),k5_relat_1('#skF_13','#skF_12'))
    | ~ v1_relat_1(k5_relat_1('#skF_13','#skF_12'))
    | ~ v1_relat_1('#skF_12')
    | ~ v1_relat_1('#skF_13') ),
    inference(superposition,[status(thm),theory(equality)],[c_14996,c_36])).

tff(c_15024,plain,(
    r2_hidden(k4_tarski(k1_funct_1('#skF_13','#skF_11'),k1_funct_1(k5_relat_1('#skF_13','#skF_12'),'#skF_11')),'#skF_12') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_56,c_176,c_274,c_15009])).

tff(c_15054,plain,
    ( k1_funct_1(k5_relat_1('#skF_13','#skF_12'),'#skF_11') = k1_funct_1('#skF_12',k1_funct_1('#skF_13','#skF_11'))
    | ~ r2_hidden(k1_funct_1('#skF_13','#skF_11'),k1_relat_1('#skF_12'))
    | ~ v1_funct_1('#skF_12')
    | ~ v1_relat_1('#skF_12') ),
    inference(resolution,[status(thm)],[c_15024,c_2])).

tff(c_15076,plain,(
    k1_funct_1(k5_relat_1('#skF_13','#skF_12'),'#skF_11') = k1_funct_1('#skF_12',k1_funct_1('#skF_13','#skF_11')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_15022,c_15054])).

tff(c_15078,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_15076])).

%------------------------------------------------------------------------------
