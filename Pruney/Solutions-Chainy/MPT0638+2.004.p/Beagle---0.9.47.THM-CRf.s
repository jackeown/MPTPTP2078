%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:37 EST 2020

% Result     : Theorem 4.14s
% Output     : CNFRefutation 4.45s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 239 expanded)
%              Number of leaves         :   30 ( 105 expanded)
%              Depth                    :   15
%              Number of atoms          :  130 ( 794 expanded)
%              Number of equality atoms :   36 ( 282 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > v1_funct_1 > k5_relat_1 > k4_tarski > k1_funct_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > #skF_11 > #skF_6 > #skF_4 > #skF_5 > #skF_3 > #skF_13 > #skF_7 > #skF_9 > #skF_2 > #skF_8 > #skF_1 > #skF_12 > #skF_10

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_11',type,(
    '#skF_11': ( $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_12',type,(
    '#skF_12': $i )).

tff('#skF_10',type,(
    '#skF_10': ( $i * $i * $i ) > $i )).

tff(f_90,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ! [B] :
            ( ( v1_relat_1(B)
              & v1_funct_1(B) )
           => ( ( k2_relat_1(A) = k1_relat_1(B)
                & k5_relat_1(A,B) = A )
             => B = k6_relat_1(k1_relat_1(B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_funct_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( B = k6_relat_1(A)
      <=> ( k1_relat_1(B) = A
          & ! [C] :
              ( r2_hidden(C,A)
             => k1_funct_1(B,C) = C ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_funct_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( B = k2_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(D,C),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).

tff(f_74,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> ( r2_hidden(A,k1_relat_1(C))
          & B = k1_funct_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).

tff(f_51,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_relat_1)).

tff(c_46,plain,(
    k6_relat_1(k1_relat_1('#skF_13')) != '#skF_13' ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_54,plain,(
    v1_relat_1('#skF_13') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_52,plain,(
    v1_funct_1('#skF_13') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_34,plain,(
    ! [B_120] :
      ( r2_hidden('#skF_11'(k1_relat_1(B_120),B_120),k1_relat_1(B_120))
      | k6_relat_1(k1_relat_1(B_120)) = B_120
      | ~ v1_funct_1(B_120)
      | ~ v1_relat_1(B_120) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_58,plain,(
    v1_relat_1('#skF_12') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_56,plain,(
    v1_funct_1('#skF_12') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_50,plain,(
    k2_relat_1('#skF_12') = k1_relat_1('#skF_13') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_71,plain,(
    ! [A_137,C_138] :
      ( r2_hidden(k4_tarski('#skF_4'(A_137,k2_relat_1(A_137),C_138),C_138),A_137)
      | ~ r2_hidden(C_138,k2_relat_1(A_137)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_80,plain,(
    ! [C_138] :
      ( r2_hidden(k4_tarski('#skF_4'('#skF_12',k1_relat_1('#skF_13'),C_138),C_138),'#skF_12')
      | ~ r2_hidden(C_138,k2_relat_1('#skF_12')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_71])).

tff(c_89,plain,(
    ! [C_142] :
      ( r2_hidden(k4_tarski('#skF_4'('#skF_12',k1_relat_1('#skF_13'),C_142),C_142),'#skF_12')
      | ~ r2_hidden(C_142,k1_relat_1('#skF_13')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_80])).

tff(c_42,plain,(
    ! [C_126,A_124,B_125] :
      ( k1_funct_1(C_126,A_124) = B_125
      | ~ r2_hidden(k4_tarski(A_124,B_125),C_126)
      | ~ v1_funct_1(C_126)
      | ~ v1_relat_1(C_126) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_92,plain,(
    ! [C_142] :
      ( k1_funct_1('#skF_12','#skF_4'('#skF_12',k1_relat_1('#skF_13'),C_142)) = C_142
      | ~ v1_funct_1('#skF_12')
      | ~ v1_relat_1('#skF_12')
      | ~ r2_hidden(C_142,k1_relat_1('#skF_13')) ) ),
    inference(resolution,[status(thm)],[c_89,c_42])).

tff(c_101,plain,(
    ! [C_142] :
      ( k1_funct_1('#skF_12','#skF_4'('#skF_12',k1_relat_1('#skF_13'),C_142)) = C_142
      | ~ r2_hidden(C_142,k1_relat_1('#skF_13')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_92])).

tff(c_83,plain,(
    ! [C_138] :
      ( r2_hidden(k4_tarski('#skF_4'('#skF_12',k1_relat_1('#skF_13'),C_138),C_138),'#skF_12')
      | ~ r2_hidden(C_138,k1_relat_1('#skF_13')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_80])).

tff(c_48,plain,(
    k5_relat_1('#skF_12','#skF_13') = '#skF_12' ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_679,plain,(
    ! [D_202,A_203,B_204,E_205] :
      ( r2_hidden(k4_tarski(D_202,'#skF_5'(k5_relat_1(A_203,B_204),B_204,E_205,A_203,D_202)),A_203)
      | ~ r2_hidden(k4_tarski(D_202,E_205),k5_relat_1(A_203,B_204))
      | ~ v1_relat_1(k5_relat_1(A_203,B_204))
      | ~ v1_relat_1(B_204)
      | ~ v1_relat_1(A_203) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_697,plain,(
    ! [D_202,E_205] :
      ( r2_hidden(k4_tarski(D_202,'#skF_5'('#skF_12','#skF_13',E_205,'#skF_12',D_202)),'#skF_12')
      | ~ r2_hidden(k4_tarski(D_202,E_205),k5_relat_1('#skF_12','#skF_13'))
      | ~ v1_relat_1(k5_relat_1('#skF_12','#skF_13'))
      | ~ v1_relat_1('#skF_13')
      | ~ v1_relat_1('#skF_12') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_679])).

tff(c_750,plain,(
    ! [D_209,E_210] :
      ( r2_hidden(k4_tarski(D_209,'#skF_5'('#skF_12','#skF_13',E_210,'#skF_12',D_209)),'#skF_12')
      | ~ r2_hidden(k4_tarski(D_209,E_210),'#skF_12') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_54,c_58,c_48,c_48,c_697])).

tff(c_758,plain,(
    ! [D_209,E_210] :
      ( k1_funct_1('#skF_12',D_209) = '#skF_5'('#skF_12','#skF_13',E_210,'#skF_12',D_209)
      | ~ v1_funct_1('#skF_12')
      | ~ v1_relat_1('#skF_12')
      | ~ r2_hidden(k4_tarski(D_209,E_210),'#skF_12') ) ),
    inference(resolution,[status(thm)],[c_750,c_42])).

tff(c_1025,plain,(
    ! [D_224,E_225] :
      ( k1_funct_1('#skF_12',D_224) = '#skF_5'('#skF_12','#skF_13',E_225,'#skF_12',D_224)
      | ~ r2_hidden(k4_tarski(D_224,E_225),'#skF_12') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_758])).

tff(c_2523,plain,(
    ! [C_286] :
      ( k1_funct_1('#skF_12','#skF_4'('#skF_12',k1_relat_1('#skF_13'),C_286)) = '#skF_5'('#skF_12','#skF_13',C_286,'#skF_12','#skF_4'('#skF_12',k1_relat_1('#skF_13'),C_286))
      | ~ r2_hidden(C_286,k1_relat_1('#skF_13')) ) ),
    inference(resolution,[status(thm)],[c_83,c_1025])).

tff(c_523,plain,(
    ! [A_193,B_194,E_195,D_196] :
      ( r2_hidden(k4_tarski('#skF_5'(k5_relat_1(A_193,B_194),B_194,E_195,A_193,D_196),E_195),B_194)
      | ~ r2_hidden(k4_tarski(D_196,E_195),k5_relat_1(A_193,B_194))
      | ~ v1_relat_1(k5_relat_1(A_193,B_194))
      | ~ v1_relat_1(B_194)
      | ~ v1_relat_1(A_193) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_544,plain,(
    ! [E_195,D_196] :
      ( r2_hidden(k4_tarski('#skF_5'('#skF_12','#skF_13',E_195,'#skF_12',D_196),E_195),'#skF_13')
      | ~ r2_hidden(k4_tarski(D_196,E_195),k5_relat_1('#skF_12','#skF_13'))
      | ~ v1_relat_1(k5_relat_1('#skF_12','#skF_13'))
      | ~ v1_relat_1('#skF_13')
      | ~ v1_relat_1('#skF_12') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_523])).

tff(c_553,plain,(
    ! [E_197,D_198] :
      ( r2_hidden(k4_tarski('#skF_5'('#skF_12','#skF_13',E_197,'#skF_12',D_198),E_197),'#skF_13')
      | ~ r2_hidden(k4_tarski(D_198,E_197),'#skF_12') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_54,c_58,c_48,c_48,c_544])).

tff(c_565,plain,(
    ! [E_197,D_198] :
      ( k1_funct_1('#skF_13','#skF_5'('#skF_12','#skF_13',E_197,'#skF_12',D_198)) = E_197
      | ~ v1_funct_1('#skF_13')
      | ~ v1_relat_1('#skF_13')
      | ~ r2_hidden(k4_tarski(D_198,E_197),'#skF_12') ) ),
    inference(resolution,[status(thm)],[c_553,c_42])).

tff(c_956,plain,(
    ! [E_217,D_218] :
      ( k1_funct_1('#skF_13','#skF_5'('#skF_12','#skF_13',E_217,'#skF_12',D_218)) = E_217
      | ~ r2_hidden(k4_tarski(D_218,E_217),'#skF_12') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_565])).

tff(c_1005,plain,(
    ! [C_138] :
      ( k1_funct_1('#skF_13','#skF_5'('#skF_12','#skF_13',C_138,'#skF_12','#skF_4'('#skF_12',k1_relat_1('#skF_13'),C_138))) = C_138
      | ~ r2_hidden(C_138,k1_relat_1('#skF_13')) ) ),
    inference(resolution,[status(thm)],[c_83,c_956])).

tff(c_2577,plain,(
    ! [C_287] :
      ( k1_funct_1('#skF_13',k1_funct_1('#skF_12','#skF_4'('#skF_12',k1_relat_1('#skF_13'),C_287))) = C_287
      | ~ r2_hidden(C_287,k1_relat_1('#skF_13'))
      | ~ r2_hidden(C_287,k1_relat_1('#skF_13')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2523,c_1005])).

tff(c_2605,plain,(
    ! [C_288] :
      ( k1_funct_1('#skF_13',C_288) = C_288
      | ~ r2_hidden(C_288,k1_relat_1('#skF_13'))
      | ~ r2_hidden(C_288,k1_relat_1('#skF_13'))
      | ~ r2_hidden(C_288,k1_relat_1('#skF_13')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_101,c_2577])).

tff(c_2671,plain,
    ( k1_funct_1('#skF_13','#skF_11'(k1_relat_1('#skF_13'),'#skF_13')) = '#skF_11'(k1_relat_1('#skF_13'),'#skF_13')
    | ~ r2_hidden('#skF_11'(k1_relat_1('#skF_13'),'#skF_13'),k1_relat_1('#skF_13'))
    | k6_relat_1(k1_relat_1('#skF_13')) = '#skF_13'
    | ~ v1_funct_1('#skF_13')
    | ~ v1_relat_1('#skF_13') ),
    inference(resolution,[status(thm)],[c_34,c_2605])).

tff(c_2707,plain,
    ( k1_funct_1('#skF_13','#skF_11'(k1_relat_1('#skF_13'),'#skF_13')) = '#skF_11'(k1_relat_1('#skF_13'),'#skF_13')
    | ~ r2_hidden('#skF_11'(k1_relat_1('#skF_13'),'#skF_13'),k1_relat_1('#skF_13'))
    | k6_relat_1(k1_relat_1('#skF_13')) = '#skF_13' ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_2671])).

tff(c_2708,plain,
    ( k1_funct_1('#skF_13','#skF_11'(k1_relat_1('#skF_13'),'#skF_13')) = '#skF_11'(k1_relat_1('#skF_13'),'#skF_13')
    | ~ r2_hidden('#skF_11'(k1_relat_1('#skF_13'),'#skF_13'),k1_relat_1('#skF_13')) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_2707])).

tff(c_2711,plain,(
    ~ r2_hidden('#skF_11'(k1_relat_1('#skF_13'),'#skF_13'),k1_relat_1('#skF_13')) ),
    inference(splitLeft,[status(thm)],[c_2708])).

tff(c_2714,plain,
    ( k6_relat_1(k1_relat_1('#skF_13')) = '#skF_13'
    | ~ v1_funct_1('#skF_13')
    | ~ v1_relat_1('#skF_13') ),
    inference(resolution,[status(thm)],[c_34,c_2711])).

tff(c_2717,plain,(
    k6_relat_1(k1_relat_1('#skF_13')) = '#skF_13' ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_2714])).

tff(c_2719,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_2717])).

tff(c_2720,plain,(
    k1_funct_1('#skF_13','#skF_11'(k1_relat_1('#skF_13'),'#skF_13')) = '#skF_11'(k1_relat_1('#skF_13'),'#skF_13') ),
    inference(splitRight,[status(thm)],[c_2708])).

tff(c_32,plain,(
    ! [B_120] :
      ( k1_funct_1(B_120,'#skF_11'(k1_relat_1(B_120),B_120)) != '#skF_11'(k1_relat_1(B_120),B_120)
      | k6_relat_1(k1_relat_1(B_120)) = B_120
      | ~ v1_funct_1(B_120)
      | ~ v1_relat_1(B_120) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_2789,plain,
    ( k6_relat_1(k1_relat_1('#skF_13')) = '#skF_13'
    | ~ v1_funct_1('#skF_13')
    | ~ v1_relat_1('#skF_13') ),
    inference(superposition,[status(thm),theory(equality)],[c_2720,c_32])).

tff(c_2802,plain,(
    k6_relat_1(k1_relat_1('#skF_13')) = '#skF_13' ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_2789])).

tff(c_2804,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_2802])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.11  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.10/0.30  % Computer   : n017.cluster.edu
% 0.10/0.30  % Model      : x86_64 x86_64
% 0.10/0.30  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.10/0.30  % Memory     : 8042.1875MB
% 0.10/0.30  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.10/0.30  % CPULimit   : 60
% 0.10/0.30  % DateTime   : Tue Dec  1 17:00:31 EST 2020
% 0.10/0.30  % CPUTime    : 
% 0.10/0.31  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.14/1.74  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.14/1.74  
% 4.14/1.74  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.14/1.74  %$ r2_hidden > v1_relat_1 > v1_funct_1 > k5_relat_1 > k4_tarski > k1_funct_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > #skF_11 > #skF_6 > #skF_4 > #skF_5 > #skF_3 > #skF_13 > #skF_7 > #skF_9 > #skF_2 > #skF_8 > #skF_1 > #skF_12 > #skF_10
% 4.14/1.74  
% 4.14/1.74  %Foreground sorts:
% 4.14/1.74  
% 4.14/1.74  
% 4.14/1.74  %Background operators:
% 4.14/1.74  
% 4.14/1.74  
% 4.14/1.74  %Foreground operators:
% 4.14/1.74  tff('#skF_11', type, '#skF_11': ($i * $i) > $i).
% 4.14/1.74  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.14/1.74  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.14/1.74  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.14/1.74  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 4.14/1.74  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 4.14/1.74  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 4.14/1.74  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 4.14/1.74  tff('#skF_5', type, '#skF_5': ($i * $i * $i * $i * $i) > $i).
% 4.14/1.74  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 4.14/1.74  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.14/1.74  tff('#skF_13', type, '#skF_13': $i).
% 4.14/1.74  tff('#skF_7', type, '#skF_7': ($i * $i * $i) > $i).
% 4.14/1.74  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 4.14/1.74  tff('#skF_9', type, '#skF_9': ($i * $i * $i) > $i).
% 4.14/1.74  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.14/1.74  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.14/1.74  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 4.14/1.74  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.14/1.74  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.14/1.74  tff('#skF_8', type, '#skF_8': ($i * $i * $i) > $i).
% 4.14/1.74  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.14/1.74  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.14/1.74  tff('#skF_12', type, '#skF_12': $i).
% 4.14/1.74  tff('#skF_10', type, '#skF_10': ($i * $i * $i) > $i).
% 4.14/1.74  
% 4.45/1.75  tff(f_90, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((k2_relat_1(A) = k1_relat_1(B)) & (k5_relat_1(A, B) = A)) => (B = k6_relat_1(k1_relat_1(B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_funct_1)).
% 4.45/1.75  tff(f_64, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((B = k6_relat_1(A)) <=> ((k1_relat_1(B) = A) & (![C]: (r2_hidden(C, A) => (k1_funct_1(B, C) = C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_funct_1)).
% 4.45/1.75  tff(f_33, axiom, (![A, B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(D, C), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_relat_1)).
% 4.45/1.75  tff(f_74, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(k4_tarski(A, B), C) <=> (r2_hidden(A, k1_relat_1(C)) & (B = k1_funct_1(C, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_funct_1)).
% 4.45/1.75  tff(f_51, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => ((C = k5_relat_1(A, B)) <=> (![D, E]: (r2_hidden(k4_tarski(D, E), C) <=> (?[F]: (r2_hidden(k4_tarski(D, F), A) & r2_hidden(k4_tarski(F, E), B)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_relat_1)).
% 4.45/1.75  tff(c_46, plain, (k6_relat_1(k1_relat_1('#skF_13'))!='#skF_13'), inference(cnfTransformation, [status(thm)], [f_90])).
% 4.45/1.75  tff(c_54, plain, (v1_relat_1('#skF_13')), inference(cnfTransformation, [status(thm)], [f_90])).
% 4.45/1.75  tff(c_52, plain, (v1_funct_1('#skF_13')), inference(cnfTransformation, [status(thm)], [f_90])).
% 4.45/1.75  tff(c_34, plain, (![B_120]: (r2_hidden('#skF_11'(k1_relat_1(B_120), B_120), k1_relat_1(B_120)) | k6_relat_1(k1_relat_1(B_120))=B_120 | ~v1_funct_1(B_120) | ~v1_relat_1(B_120))), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.45/1.75  tff(c_58, plain, (v1_relat_1('#skF_12')), inference(cnfTransformation, [status(thm)], [f_90])).
% 4.45/1.75  tff(c_56, plain, (v1_funct_1('#skF_12')), inference(cnfTransformation, [status(thm)], [f_90])).
% 4.45/1.75  tff(c_50, plain, (k2_relat_1('#skF_12')=k1_relat_1('#skF_13')), inference(cnfTransformation, [status(thm)], [f_90])).
% 4.45/1.76  tff(c_71, plain, (![A_137, C_138]: (r2_hidden(k4_tarski('#skF_4'(A_137, k2_relat_1(A_137), C_138), C_138), A_137) | ~r2_hidden(C_138, k2_relat_1(A_137)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.45/1.76  tff(c_80, plain, (![C_138]: (r2_hidden(k4_tarski('#skF_4'('#skF_12', k1_relat_1('#skF_13'), C_138), C_138), '#skF_12') | ~r2_hidden(C_138, k2_relat_1('#skF_12')))), inference(superposition, [status(thm), theory('equality')], [c_50, c_71])).
% 4.45/1.76  tff(c_89, plain, (![C_142]: (r2_hidden(k4_tarski('#skF_4'('#skF_12', k1_relat_1('#skF_13'), C_142), C_142), '#skF_12') | ~r2_hidden(C_142, k1_relat_1('#skF_13')))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_80])).
% 4.45/1.76  tff(c_42, plain, (![C_126, A_124, B_125]: (k1_funct_1(C_126, A_124)=B_125 | ~r2_hidden(k4_tarski(A_124, B_125), C_126) | ~v1_funct_1(C_126) | ~v1_relat_1(C_126))), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.45/1.76  tff(c_92, plain, (![C_142]: (k1_funct_1('#skF_12', '#skF_4'('#skF_12', k1_relat_1('#skF_13'), C_142))=C_142 | ~v1_funct_1('#skF_12') | ~v1_relat_1('#skF_12') | ~r2_hidden(C_142, k1_relat_1('#skF_13')))), inference(resolution, [status(thm)], [c_89, c_42])).
% 4.45/1.76  tff(c_101, plain, (![C_142]: (k1_funct_1('#skF_12', '#skF_4'('#skF_12', k1_relat_1('#skF_13'), C_142))=C_142 | ~r2_hidden(C_142, k1_relat_1('#skF_13')))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_92])).
% 4.45/1.76  tff(c_83, plain, (![C_138]: (r2_hidden(k4_tarski('#skF_4'('#skF_12', k1_relat_1('#skF_13'), C_138), C_138), '#skF_12') | ~r2_hidden(C_138, k1_relat_1('#skF_13')))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_80])).
% 4.45/1.76  tff(c_48, plain, (k5_relat_1('#skF_12', '#skF_13')='#skF_12'), inference(cnfTransformation, [status(thm)], [f_90])).
% 4.45/1.76  tff(c_679, plain, (![D_202, A_203, B_204, E_205]: (r2_hidden(k4_tarski(D_202, '#skF_5'(k5_relat_1(A_203, B_204), B_204, E_205, A_203, D_202)), A_203) | ~r2_hidden(k4_tarski(D_202, E_205), k5_relat_1(A_203, B_204)) | ~v1_relat_1(k5_relat_1(A_203, B_204)) | ~v1_relat_1(B_204) | ~v1_relat_1(A_203))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.45/1.76  tff(c_697, plain, (![D_202, E_205]: (r2_hidden(k4_tarski(D_202, '#skF_5'('#skF_12', '#skF_13', E_205, '#skF_12', D_202)), '#skF_12') | ~r2_hidden(k4_tarski(D_202, E_205), k5_relat_1('#skF_12', '#skF_13')) | ~v1_relat_1(k5_relat_1('#skF_12', '#skF_13')) | ~v1_relat_1('#skF_13') | ~v1_relat_1('#skF_12'))), inference(superposition, [status(thm), theory('equality')], [c_48, c_679])).
% 4.45/1.76  tff(c_750, plain, (![D_209, E_210]: (r2_hidden(k4_tarski(D_209, '#skF_5'('#skF_12', '#skF_13', E_210, '#skF_12', D_209)), '#skF_12') | ~r2_hidden(k4_tarski(D_209, E_210), '#skF_12'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_54, c_58, c_48, c_48, c_697])).
% 4.45/1.76  tff(c_758, plain, (![D_209, E_210]: (k1_funct_1('#skF_12', D_209)='#skF_5'('#skF_12', '#skF_13', E_210, '#skF_12', D_209) | ~v1_funct_1('#skF_12') | ~v1_relat_1('#skF_12') | ~r2_hidden(k4_tarski(D_209, E_210), '#skF_12'))), inference(resolution, [status(thm)], [c_750, c_42])).
% 4.45/1.76  tff(c_1025, plain, (![D_224, E_225]: (k1_funct_1('#skF_12', D_224)='#skF_5'('#skF_12', '#skF_13', E_225, '#skF_12', D_224) | ~r2_hidden(k4_tarski(D_224, E_225), '#skF_12'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_758])).
% 4.45/1.76  tff(c_2523, plain, (![C_286]: (k1_funct_1('#skF_12', '#skF_4'('#skF_12', k1_relat_1('#skF_13'), C_286))='#skF_5'('#skF_12', '#skF_13', C_286, '#skF_12', '#skF_4'('#skF_12', k1_relat_1('#skF_13'), C_286)) | ~r2_hidden(C_286, k1_relat_1('#skF_13')))), inference(resolution, [status(thm)], [c_83, c_1025])).
% 4.45/1.76  tff(c_523, plain, (![A_193, B_194, E_195, D_196]: (r2_hidden(k4_tarski('#skF_5'(k5_relat_1(A_193, B_194), B_194, E_195, A_193, D_196), E_195), B_194) | ~r2_hidden(k4_tarski(D_196, E_195), k5_relat_1(A_193, B_194)) | ~v1_relat_1(k5_relat_1(A_193, B_194)) | ~v1_relat_1(B_194) | ~v1_relat_1(A_193))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.45/1.76  tff(c_544, plain, (![E_195, D_196]: (r2_hidden(k4_tarski('#skF_5'('#skF_12', '#skF_13', E_195, '#skF_12', D_196), E_195), '#skF_13') | ~r2_hidden(k4_tarski(D_196, E_195), k5_relat_1('#skF_12', '#skF_13')) | ~v1_relat_1(k5_relat_1('#skF_12', '#skF_13')) | ~v1_relat_1('#skF_13') | ~v1_relat_1('#skF_12'))), inference(superposition, [status(thm), theory('equality')], [c_48, c_523])).
% 4.45/1.76  tff(c_553, plain, (![E_197, D_198]: (r2_hidden(k4_tarski('#skF_5'('#skF_12', '#skF_13', E_197, '#skF_12', D_198), E_197), '#skF_13') | ~r2_hidden(k4_tarski(D_198, E_197), '#skF_12'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_54, c_58, c_48, c_48, c_544])).
% 4.45/1.76  tff(c_565, plain, (![E_197, D_198]: (k1_funct_1('#skF_13', '#skF_5'('#skF_12', '#skF_13', E_197, '#skF_12', D_198))=E_197 | ~v1_funct_1('#skF_13') | ~v1_relat_1('#skF_13') | ~r2_hidden(k4_tarski(D_198, E_197), '#skF_12'))), inference(resolution, [status(thm)], [c_553, c_42])).
% 4.45/1.76  tff(c_956, plain, (![E_217, D_218]: (k1_funct_1('#skF_13', '#skF_5'('#skF_12', '#skF_13', E_217, '#skF_12', D_218))=E_217 | ~r2_hidden(k4_tarski(D_218, E_217), '#skF_12'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_565])).
% 4.45/1.76  tff(c_1005, plain, (![C_138]: (k1_funct_1('#skF_13', '#skF_5'('#skF_12', '#skF_13', C_138, '#skF_12', '#skF_4'('#skF_12', k1_relat_1('#skF_13'), C_138)))=C_138 | ~r2_hidden(C_138, k1_relat_1('#skF_13')))), inference(resolution, [status(thm)], [c_83, c_956])).
% 4.45/1.76  tff(c_2577, plain, (![C_287]: (k1_funct_1('#skF_13', k1_funct_1('#skF_12', '#skF_4'('#skF_12', k1_relat_1('#skF_13'), C_287)))=C_287 | ~r2_hidden(C_287, k1_relat_1('#skF_13')) | ~r2_hidden(C_287, k1_relat_1('#skF_13')))), inference(superposition, [status(thm), theory('equality')], [c_2523, c_1005])).
% 4.45/1.76  tff(c_2605, plain, (![C_288]: (k1_funct_1('#skF_13', C_288)=C_288 | ~r2_hidden(C_288, k1_relat_1('#skF_13')) | ~r2_hidden(C_288, k1_relat_1('#skF_13')) | ~r2_hidden(C_288, k1_relat_1('#skF_13')))), inference(superposition, [status(thm), theory('equality')], [c_101, c_2577])).
% 4.45/1.76  tff(c_2671, plain, (k1_funct_1('#skF_13', '#skF_11'(k1_relat_1('#skF_13'), '#skF_13'))='#skF_11'(k1_relat_1('#skF_13'), '#skF_13') | ~r2_hidden('#skF_11'(k1_relat_1('#skF_13'), '#skF_13'), k1_relat_1('#skF_13')) | k6_relat_1(k1_relat_1('#skF_13'))='#skF_13' | ~v1_funct_1('#skF_13') | ~v1_relat_1('#skF_13')), inference(resolution, [status(thm)], [c_34, c_2605])).
% 4.45/1.76  tff(c_2707, plain, (k1_funct_1('#skF_13', '#skF_11'(k1_relat_1('#skF_13'), '#skF_13'))='#skF_11'(k1_relat_1('#skF_13'), '#skF_13') | ~r2_hidden('#skF_11'(k1_relat_1('#skF_13'), '#skF_13'), k1_relat_1('#skF_13')) | k6_relat_1(k1_relat_1('#skF_13'))='#skF_13'), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_2671])).
% 4.45/1.76  tff(c_2708, plain, (k1_funct_1('#skF_13', '#skF_11'(k1_relat_1('#skF_13'), '#skF_13'))='#skF_11'(k1_relat_1('#skF_13'), '#skF_13') | ~r2_hidden('#skF_11'(k1_relat_1('#skF_13'), '#skF_13'), k1_relat_1('#skF_13'))), inference(negUnitSimplification, [status(thm)], [c_46, c_2707])).
% 4.45/1.76  tff(c_2711, plain, (~r2_hidden('#skF_11'(k1_relat_1('#skF_13'), '#skF_13'), k1_relat_1('#skF_13'))), inference(splitLeft, [status(thm)], [c_2708])).
% 4.45/1.76  tff(c_2714, plain, (k6_relat_1(k1_relat_1('#skF_13'))='#skF_13' | ~v1_funct_1('#skF_13') | ~v1_relat_1('#skF_13')), inference(resolution, [status(thm)], [c_34, c_2711])).
% 4.45/1.76  tff(c_2717, plain, (k6_relat_1(k1_relat_1('#skF_13'))='#skF_13'), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_2714])).
% 4.45/1.76  tff(c_2719, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_2717])).
% 4.45/1.76  tff(c_2720, plain, (k1_funct_1('#skF_13', '#skF_11'(k1_relat_1('#skF_13'), '#skF_13'))='#skF_11'(k1_relat_1('#skF_13'), '#skF_13')), inference(splitRight, [status(thm)], [c_2708])).
% 4.45/1.76  tff(c_32, plain, (![B_120]: (k1_funct_1(B_120, '#skF_11'(k1_relat_1(B_120), B_120))!='#skF_11'(k1_relat_1(B_120), B_120) | k6_relat_1(k1_relat_1(B_120))=B_120 | ~v1_funct_1(B_120) | ~v1_relat_1(B_120))), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.45/1.76  tff(c_2789, plain, (k6_relat_1(k1_relat_1('#skF_13'))='#skF_13' | ~v1_funct_1('#skF_13') | ~v1_relat_1('#skF_13')), inference(superposition, [status(thm), theory('equality')], [c_2720, c_32])).
% 4.45/1.76  tff(c_2802, plain, (k6_relat_1(k1_relat_1('#skF_13'))='#skF_13'), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_2789])).
% 4.45/1.76  tff(c_2804, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_2802])).
% 4.45/1.76  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.45/1.76  
% 4.45/1.76  Inference rules
% 4.45/1.76  ----------------------
% 4.45/1.76  #Ref     : 0
% 4.45/1.76  #Sup     : 523
% 4.45/1.76  #Fact    : 0
% 4.45/1.76  #Define  : 0
% 4.45/1.76  #Split   : 2
% 4.45/1.76  #Chain   : 0
% 4.45/1.76  #Close   : 0
% 4.45/1.76  
% 4.45/1.76  Ordering : KBO
% 4.45/1.76  
% 4.45/1.76  Simplification rules
% 4.45/1.76  ----------------------
% 4.45/1.76  #Subsume      : 60
% 4.45/1.76  #Demod        : 452
% 4.45/1.76  #Tautology    : 119
% 4.45/1.76  #SimpNegUnit  : 3
% 4.45/1.76  #BackRed      : 8
% 4.45/1.76  
% 4.45/1.76  #Partial instantiations: 0
% 4.45/1.76  #Strategies tried      : 1
% 4.45/1.76  
% 4.45/1.76  Timing (in seconds)
% 4.45/1.76  ----------------------
% 4.45/1.76  Preprocessing        : 0.31
% 4.45/1.76  Parsing              : 0.15
% 4.45/1.76  CNF conversion       : 0.03
% 4.45/1.76  Main loop            : 0.71
% 4.45/1.76  Inferencing          : 0.26
% 4.45/1.76  Reduction            : 0.22
% 4.45/1.76  Demodulation         : 0.16
% 4.45/1.76  BG Simplification    : 0.04
% 4.45/1.76  Subsumption          : 0.13
% 4.45/1.76  Abstraction          : 0.04
% 4.45/1.76  MUC search           : 0.00
% 4.45/1.76  Cooper               : 0.00
% 4.45/1.76  Total                : 1.05
% 4.45/1.76  Index Insertion      : 0.00
% 4.45/1.76  Index Deletion       : 0.00
% 4.45/1.76  Index Matching       : 0.00
% 4.45/1.76  BG Taut test         : 0.00
%------------------------------------------------------------------------------
