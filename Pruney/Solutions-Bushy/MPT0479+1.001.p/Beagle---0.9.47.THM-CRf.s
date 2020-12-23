%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0479+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:36:22 EST 2020

% Result     : Theorem 2.71s
% Output     : CNFRefutation 3.12s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 186 expanded)
%              Number of leaves         :   27 (  73 expanded)
%              Depth                    :   10
%              Number of atoms          :  156 ( 443 expanded)
%              Number of equality atoms :   10 (  21 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > k5_relat_1 > k4_tarski > #nlpp > k6_relat_1 > #skF_11 > #skF_6 > #skF_5 > #skF_3 > #skF_14 > #skF_13 > #skF_7 > #skF_9 > #skF_2 > #skF_8 > #skF_1 > #skF_12 > #skF_4 > #skF_10

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff('#skF_14',type,(
    '#skF_14': $i )).

tff('#skF_13',type,(
    '#skF_13': $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_12',type,(
    '#skF_12': $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': ( $i * $i * $i ) > $i )).

tff(f_61,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_70,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( v1_relat_1(D)
       => ( r2_hidden(k4_tarski(A,B),k5_relat_1(k6_relat_1(C),D))
        <=> ( r2_hidden(A,C)
            & r2_hidden(k4_tarski(A,B),D) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_relat_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k5_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( B = k6_relat_1(A)
      <=> ! [C,D] :
            ( r2_hidden(k4_tarski(C,D),B)
          <=> ( r2_hidden(C,A)
              & C = D ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_relat_1)).

tff(f_53,axiom,(
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

tff(c_40,plain,(
    ! [A_110] : v1_relat_1(k6_relat_1(A_110)) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_42,plain,(
    v1_relat_1('#skF_14') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_38,plain,(
    ! [A_108,B_109] :
      ( v1_relat_1(k5_relat_1(A_108,B_109))
      | ~ v1_relat_1(B_109)
      | ~ v1_relat_1(A_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_50,plain,
    ( r2_hidden(k4_tarski('#skF_11','#skF_12'),k5_relat_1(k6_relat_1('#skF_13'),'#skF_14'))
    | r2_hidden(k4_tarski('#skF_11','#skF_12'),'#skF_14') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_76,plain,(
    r2_hidden(k4_tarski('#skF_11','#skF_12'),'#skF_14') ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_54,plain,
    ( r2_hidden(k4_tarski('#skF_11','#skF_12'),k5_relat_1(k6_relat_1('#skF_13'),'#skF_14'))
    | r2_hidden('#skF_11','#skF_13') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_75,plain,(
    r2_hidden('#skF_11','#skF_13') ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_14,plain,(
    ! [D_8,A_1] :
      ( r2_hidden(k4_tarski(D_8,D_8),k6_relat_1(A_1))
      | ~ r2_hidden(D_8,A_1)
      | ~ v1_relat_1(k6_relat_1(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_60,plain,(
    ! [D_8,A_1] :
      ( r2_hidden(k4_tarski(D_8,D_8),k6_relat_1(A_1))
      | ~ r2_hidden(D_8,A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_14])).

tff(c_215,plain,(
    ! [A_152,B_150,F_149,E_148,D_151] :
      ( r2_hidden(k4_tarski(D_151,E_148),k5_relat_1(A_152,B_150))
      | ~ r2_hidden(k4_tarski(F_149,E_148),B_150)
      | ~ r2_hidden(k4_tarski(D_151,F_149),A_152)
      | ~ v1_relat_1(k5_relat_1(A_152,B_150))
      | ~ v1_relat_1(B_150)
      | ~ v1_relat_1(A_152) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_225,plain,(
    ! [D_151,A_152] :
      ( r2_hidden(k4_tarski(D_151,'#skF_12'),k5_relat_1(A_152,'#skF_14'))
      | ~ r2_hidden(k4_tarski(D_151,'#skF_11'),A_152)
      | ~ v1_relat_1(k5_relat_1(A_152,'#skF_14'))
      | ~ v1_relat_1('#skF_14')
      | ~ v1_relat_1(A_152) ) ),
    inference(resolution,[status(thm)],[c_76,c_215])).

tff(c_240,plain,(
    ! [D_153,A_154] :
      ( r2_hidden(k4_tarski(D_153,'#skF_12'),k5_relat_1(A_154,'#skF_14'))
      | ~ r2_hidden(k4_tarski(D_153,'#skF_11'),A_154)
      | ~ v1_relat_1(k5_relat_1(A_154,'#skF_14'))
      | ~ v1_relat_1(A_154) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_225])).

tff(c_44,plain,
    ( ~ r2_hidden(k4_tarski('#skF_11','#skF_12'),'#skF_14')
    | ~ r2_hidden('#skF_11','#skF_13')
    | ~ r2_hidden(k4_tarski('#skF_11','#skF_12'),k5_relat_1(k6_relat_1('#skF_13'),'#skF_14')) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_78,plain,
    ( ~ r2_hidden(k4_tarski('#skF_11','#skF_12'),'#skF_14')
    | ~ r2_hidden(k4_tarski('#skF_11','#skF_12'),k5_relat_1(k6_relat_1('#skF_13'),'#skF_14')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_44])).

tff(c_79,plain,(
    ~ r2_hidden(k4_tarski('#skF_11','#skF_12'),k5_relat_1(k6_relat_1('#skF_13'),'#skF_14')) ),
    inference(splitLeft,[status(thm)],[c_78])).

tff(c_245,plain,
    ( ~ r2_hidden(k4_tarski('#skF_11','#skF_11'),k6_relat_1('#skF_13'))
    | ~ v1_relat_1(k5_relat_1(k6_relat_1('#skF_13'),'#skF_14'))
    | ~ v1_relat_1(k6_relat_1('#skF_13')) ),
    inference(resolution,[status(thm)],[c_240,c_79])).

tff(c_249,plain,
    ( ~ r2_hidden(k4_tarski('#skF_11','#skF_11'),k6_relat_1('#skF_13'))
    | ~ v1_relat_1(k5_relat_1(k6_relat_1('#skF_13'),'#skF_14')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_245])).

tff(c_250,plain,(
    ~ v1_relat_1(k5_relat_1(k6_relat_1('#skF_13'),'#skF_14')) ),
    inference(splitLeft,[status(thm)],[c_249])).

tff(c_253,plain,
    ( ~ v1_relat_1('#skF_14')
    | ~ v1_relat_1(k6_relat_1('#skF_13')) ),
    inference(resolution,[status(thm)],[c_38,c_250])).

tff(c_257,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_42,c_253])).

tff(c_258,plain,(
    ~ r2_hidden(k4_tarski('#skF_11','#skF_11'),k6_relat_1('#skF_13')) ),
    inference(splitRight,[status(thm)],[c_249])).

tff(c_290,plain,(
    ~ r2_hidden('#skF_11','#skF_13') ),
    inference(resolution,[status(thm)],[c_60,c_258])).

tff(c_294,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_290])).

tff(c_295,plain,(
    ~ r2_hidden(k4_tarski('#skF_11','#skF_12'),'#skF_14') ),
    inference(splitRight,[status(thm)],[c_78])).

tff(c_298,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_295])).

tff(c_300,plain,(
    ~ r2_hidden(k4_tarski('#skF_11','#skF_12'),'#skF_14') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_299,plain,(
    r2_hidden(k4_tarski('#skF_11','#skF_12'),k5_relat_1(k6_relat_1('#skF_13'),'#skF_14')) ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_437,plain,(
    ! [F_184,B_185,A_187,D_186,E_183] :
      ( r2_hidden(k4_tarski(D_186,E_183),k5_relat_1(A_187,B_185))
      | ~ r2_hidden(k4_tarski(F_184,E_183),B_185)
      | ~ r2_hidden(k4_tarski(D_186,F_184),A_187)
      | ~ v1_relat_1(k5_relat_1(A_187,B_185))
      | ~ v1_relat_1(B_185)
      | ~ v1_relat_1(A_187) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_456,plain,(
    ! [D_186,A_187] :
      ( r2_hidden(k4_tarski(D_186,'#skF_12'),k5_relat_1(A_187,k5_relat_1(k6_relat_1('#skF_13'),'#skF_14')))
      | ~ r2_hidden(k4_tarski(D_186,'#skF_11'),A_187)
      | ~ v1_relat_1(k5_relat_1(A_187,k5_relat_1(k6_relat_1('#skF_13'),'#skF_14')))
      | ~ v1_relat_1(k5_relat_1(k6_relat_1('#skF_13'),'#skF_14'))
      | ~ v1_relat_1(A_187) ) ),
    inference(resolution,[status(thm)],[c_299,c_437])).

tff(c_609,plain,(
    ~ v1_relat_1(k5_relat_1(k6_relat_1('#skF_13'),'#skF_14')) ),
    inference(splitLeft,[status(thm)],[c_456])).

tff(c_612,plain,
    ( ~ v1_relat_1('#skF_14')
    | ~ v1_relat_1(k6_relat_1('#skF_13')) ),
    inference(resolution,[status(thm)],[c_38,c_609])).

tff(c_616,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_42,c_612])).

tff(c_618,plain,(
    v1_relat_1(k5_relat_1(k6_relat_1('#skF_13'),'#skF_14')) ),
    inference(splitRight,[status(thm)],[c_456])).

tff(c_496,plain,(
    ! [D_202,E_203,B_204,A_205] :
      ( r2_hidden(k4_tarski(D_202,'#skF_5'(E_203,B_204,D_202,A_205,k5_relat_1(A_205,B_204))),A_205)
      | ~ r2_hidden(k4_tarski(D_202,E_203),k5_relat_1(A_205,B_204))
      | ~ v1_relat_1(k5_relat_1(A_205,B_204))
      | ~ v1_relat_1(B_204)
      | ~ v1_relat_1(A_205) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_16,plain,(
    ! [D_8,C_7,A_1] :
      ( D_8 = C_7
      | ~ r2_hidden(k4_tarski(C_7,D_8),k6_relat_1(A_1))
      | ~ v1_relat_1(k6_relat_1(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_58,plain,(
    ! [D_8,C_7,A_1] :
      ( D_8 = C_7
      | ~ r2_hidden(k4_tarski(C_7,D_8),k6_relat_1(A_1)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_16])).

tff(c_506,plain,(
    ! [E_203,B_204,D_202,A_1] :
      ( '#skF_5'(E_203,B_204,D_202,k6_relat_1(A_1),k5_relat_1(k6_relat_1(A_1),B_204)) = D_202
      | ~ r2_hidden(k4_tarski(D_202,E_203),k5_relat_1(k6_relat_1(A_1),B_204))
      | ~ v1_relat_1(k5_relat_1(k6_relat_1(A_1),B_204))
      | ~ v1_relat_1(B_204)
      | ~ v1_relat_1(k6_relat_1(A_1)) ) ),
    inference(resolution,[status(thm)],[c_496,c_58])).

tff(c_577,plain,(
    ! [E_214,B_215,D_216,A_217] :
      ( '#skF_5'(E_214,B_215,D_216,k6_relat_1(A_217),k5_relat_1(k6_relat_1(A_217),B_215)) = D_216
      | ~ r2_hidden(k4_tarski(D_216,E_214),k5_relat_1(k6_relat_1(A_217),B_215))
      | ~ v1_relat_1(k5_relat_1(k6_relat_1(A_217),B_215))
      | ~ v1_relat_1(B_215) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_506])).

tff(c_597,plain,
    ( '#skF_5'('#skF_12','#skF_14','#skF_11',k6_relat_1('#skF_13'),k5_relat_1(k6_relat_1('#skF_13'),'#skF_14')) = '#skF_11'
    | ~ v1_relat_1(k5_relat_1(k6_relat_1('#skF_13'),'#skF_14'))
    | ~ v1_relat_1('#skF_14') ),
    inference(resolution,[status(thm)],[c_299,c_577])).

tff(c_608,plain,
    ( '#skF_5'('#skF_12','#skF_14','#skF_11',k6_relat_1('#skF_13'),k5_relat_1(k6_relat_1('#skF_13'),'#skF_14')) = '#skF_11'
    | ~ v1_relat_1(k5_relat_1(k6_relat_1('#skF_13'),'#skF_14')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_597])).

tff(c_620,plain,(
    '#skF_5'('#skF_12','#skF_14','#skF_11',k6_relat_1('#skF_13'),k5_relat_1(k6_relat_1('#skF_13'),'#skF_14')) = '#skF_11' ),
    inference(demodulation,[status(thm),theory(equality)],[c_618,c_608])).

tff(c_34,plain,(
    ! [E_101,B_61,D_100,A_9] :
      ( r2_hidden(k4_tarski('#skF_5'(E_101,B_61,D_100,A_9,k5_relat_1(A_9,B_61)),E_101),B_61)
      | ~ r2_hidden(k4_tarski(D_100,E_101),k5_relat_1(A_9,B_61))
      | ~ v1_relat_1(k5_relat_1(A_9,B_61))
      | ~ v1_relat_1(B_61)
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_627,plain,
    ( r2_hidden(k4_tarski('#skF_11','#skF_12'),'#skF_14')
    | ~ r2_hidden(k4_tarski('#skF_11','#skF_12'),k5_relat_1(k6_relat_1('#skF_13'),'#skF_14'))
    | ~ v1_relat_1(k5_relat_1(k6_relat_1('#skF_13'),'#skF_14'))
    | ~ v1_relat_1('#skF_14')
    | ~ v1_relat_1(k6_relat_1('#skF_13')) ),
    inference(superposition,[status(thm),theory(equality)],[c_620,c_34])).

tff(c_633,plain,(
    r2_hidden(k4_tarski('#skF_11','#skF_12'),'#skF_14') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_42,c_618,c_299,c_627])).

tff(c_635,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_300,c_633])).

tff(c_637,plain,(
    ~ r2_hidden('#skF_11','#skF_13') ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_636,plain,(
    r2_hidden(k4_tarski('#skF_11','#skF_12'),k5_relat_1(k6_relat_1('#skF_13'),'#skF_14')) ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_834,plain,(
    ! [D_261,E_262,B_263,A_264] :
      ( r2_hidden(k4_tarski(D_261,'#skF_5'(E_262,B_263,D_261,A_264,k5_relat_1(A_264,B_263))),A_264)
      | ~ r2_hidden(k4_tarski(D_261,E_262),k5_relat_1(A_264,B_263))
      | ~ v1_relat_1(k5_relat_1(A_264,B_263))
      | ~ v1_relat_1(B_263)
      | ~ v1_relat_1(A_264) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_18,plain,(
    ! [C_7,A_1,D_8] :
      ( r2_hidden(C_7,A_1)
      | ~ r2_hidden(k4_tarski(C_7,D_8),k6_relat_1(A_1))
      | ~ v1_relat_1(k6_relat_1(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_56,plain,(
    ! [C_7,A_1,D_8] :
      ( r2_hidden(C_7,A_1)
      | ~ r2_hidden(k4_tarski(C_7,D_8),k6_relat_1(A_1)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_18])).

tff(c_840,plain,(
    ! [D_261,A_1,E_262,B_263] :
      ( r2_hidden(D_261,A_1)
      | ~ r2_hidden(k4_tarski(D_261,E_262),k5_relat_1(k6_relat_1(A_1),B_263))
      | ~ v1_relat_1(k5_relat_1(k6_relat_1(A_1),B_263))
      | ~ v1_relat_1(B_263)
      | ~ v1_relat_1(k6_relat_1(A_1)) ) ),
    inference(resolution,[status(thm)],[c_834,c_56])).

tff(c_852,plain,(
    ! [D_265,A_266,E_267,B_268] :
      ( r2_hidden(D_265,A_266)
      | ~ r2_hidden(k4_tarski(D_265,E_267),k5_relat_1(k6_relat_1(A_266),B_268))
      | ~ v1_relat_1(k5_relat_1(k6_relat_1(A_266),B_268))
      | ~ v1_relat_1(B_268) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_840])).

tff(c_879,plain,
    ( r2_hidden('#skF_11','#skF_13')
    | ~ v1_relat_1(k5_relat_1(k6_relat_1('#skF_13'),'#skF_14'))
    | ~ v1_relat_1('#skF_14') ),
    inference(resolution,[status(thm)],[c_636,c_852])).

tff(c_890,plain,
    ( r2_hidden('#skF_11','#skF_13')
    | ~ v1_relat_1(k5_relat_1(k6_relat_1('#skF_13'),'#skF_14')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_879])).

tff(c_891,plain,(
    ~ v1_relat_1(k5_relat_1(k6_relat_1('#skF_13'),'#skF_14')) ),
    inference(negUnitSimplification,[status(thm)],[c_637,c_890])).

tff(c_894,plain,
    ( ~ v1_relat_1('#skF_14')
    | ~ v1_relat_1(k6_relat_1('#skF_13')) ),
    inference(resolution,[status(thm)],[c_38,c_891])).

tff(c_898,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_42,c_894])).

%------------------------------------------------------------------------------
