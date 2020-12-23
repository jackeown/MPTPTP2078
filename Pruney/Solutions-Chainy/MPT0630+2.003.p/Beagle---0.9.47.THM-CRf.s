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
% DateTime   : Thu Dec  3 10:03:18 EST 2020

% Result     : Theorem 14.33s
% Output     : CNFRefutation 14.33s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 175 expanded)
%              Number of leaves         :   36 (  81 expanded)
%              Depth                    :   17
%              Number of atoms          :  160 ( 483 expanded)
%              Number of equality atoms :   12 (  62 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k5_relat_1 > k4_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_13 > #skF_6 > #skF_17 > #skF_12 > #skF_3 > #skF_16 > #skF_5 > #skF_8 > #skF_10 > #skF_11 > #skF_9 > #skF_15 > #skF_14 > #skF_2 > #skF_7 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_13',type,(
    '#skF_13': ( $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff('#skF_17',type,(
    '#skF_17': $i )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff('#skF_12',type,(
    '#skF_12': ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_16',type,(
    '#skF_16': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_11',type,(
    '#skF_11': ( $i * $i * $i ) > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': ( $i * $i * $i ) > $i )).

tff('#skF_15',type,(
    '#skF_15': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_14',type,(
    '#skF_14': ( $i * $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_96,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ! [B] :
            ( ( v1_relat_1(B)
              & v1_funct_1(B) )
           => ( k1_relat_1(k5_relat_1(B,A)) = k1_relat_1(B)
             => r1_tarski(k2_relat_1(B),k1_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_funct_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_48,axiom,(
    ! [A,B] :
      ( B = k2_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(D,C),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

tff(f_82,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> ( r2_hidden(A,k1_relat_1(C))
          & B = k1_funct_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).

tff(f_72,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k5_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

tff(f_66,axiom,(
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

tff(c_58,plain,(
    ~ r1_tarski(k2_relat_1('#skF_17'),k1_relat_1('#skF_16')) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_98,plain,(
    ! [A_170,C_171] :
      ( r2_hidden(k4_tarski('#skF_9'(A_170,k2_relat_1(A_170),C_171),C_171),A_170)
      | ~ r2_hidden(C_171,k2_relat_1(A_170)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_10,plain,(
    ! [C_21,A_6,D_24] :
      ( r2_hidden(C_21,k1_relat_1(A_6))
      | ~ r2_hidden(k4_tarski(C_21,D_24),A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_107,plain,(
    ! [A_170,C_171] :
      ( r2_hidden('#skF_9'(A_170,k2_relat_1(A_170),C_171),k1_relat_1(A_170))
      | ~ r2_hidden(C_171,k2_relat_1(A_170)) ) ),
    inference(resolution,[status(thm)],[c_98,c_10])).

tff(c_64,plain,(
    v1_relat_1('#skF_17') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_62,plain,(
    v1_funct_1('#skF_17') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_20,plain,(
    ! [A_25,C_40] :
      ( r2_hidden(k4_tarski('#skF_9'(A_25,k2_relat_1(A_25),C_40),C_40),A_25)
      | ~ r2_hidden(C_40,k2_relat_1(A_25)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_117,plain,(
    ! [C_174,A_175,B_176] :
      ( k1_funct_1(C_174,A_175) = B_176
      | ~ r2_hidden(k4_tarski(A_175,B_176),C_174)
      | ~ v1_funct_1(C_174)
      | ~ v1_relat_1(C_174) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_121,plain,(
    ! [A_25,C_40] :
      ( k1_funct_1(A_25,'#skF_9'(A_25,k2_relat_1(A_25),C_40)) = C_40
      | ~ v1_funct_1(A_25)
      | ~ v1_relat_1(A_25)
      | ~ r2_hidden(C_40,k2_relat_1(A_25)) ) ),
    inference(resolution,[status(thm)],[c_20,c_117])).

tff(c_75,plain,(
    ! [A_153,B_154] :
      ( ~ r2_hidden('#skF_1'(A_153,B_154),B_154)
      | r1_tarski(A_153,B_154) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_80,plain,(
    ! [A_1] : r1_tarski(A_1,A_1) ),
    inference(resolution,[status(thm)],[c_6,c_75])).

tff(c_60,plain,(
    k1_relat_1(k5_relat_1('#skF_17','#skF_16')) = k1_relat_1('#skF_17') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_127,plain,(
    ! [C_180,A_181] :
      ( r2_hidden(k4_tarski(C_180,'#skF_5'(A_181,k1_relat_1(A_181),C_180)),A_181)
      | ~ r2_hidden(C_180,k1_relat_1(A_181)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_238,plain,(
    ! [C_207,A_208,B_209] :
      ( r2_hidden(k4_tarski(C_207,'#skF_5'(A_208,k1_relat_1(A_208),C_207)),B_209)
      | ~ r1_tarski(A_208,B_209)
      | ~ r2_hidden(C_207,k1_relat_1(A_208)) ) ),
    inference(resolution,[status(thm)],[c_127,c_2])).

tff(c_255,plain,(
    ! [C_207,B_209] :
      ( r2_hidden(k4_tarski(C_207,'#skF_5'(k5_relat_1('#skF_17','#skF_16'),k1_relat_1('#skF_17'),C_207)),B_209)
      | ~ r1_tarski(k5_relat_1('#skF_17','#skF_16'),B_209)
      | ~ r2_hidden(C_207,k1_relat_1(k5_relat_1('#skF_17','#skF_16'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_238])).

tff(c_261,plain,(
    ! [C_207,B_209] :
      ( r2_hidden(k4_tarski(C_207,'#skF_5'(k5_relat_1('#skF_17','#skF_16'),k1_relat_1('#skF_17'),C_207)),B_209)
      | ~ r1_tarski(k5_relat_1('#skF_17','#skF_16'),B_209)
      | ~ r2_hidden(C_207,k1_relat_1('#skF_17')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_255])).

tff(c_68,plain,(
    v1_relat_1('#skF_16') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_50,plain,(
    ! [A_143,B_144] :
      ( v1_relat_1(k5_relat_1(A_143,B_144))
      | ~ v1_relat_1(B_144)
      | ~ v1_relat_1(A_143) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_141,plain,(
    ! [C_180] :
      ( r2_hidden(k4_tarski(C_180,'#skF_5'(k5_relat_1('#skF_17','#skF_16'),k1_relat_1('#skF_17'),C_180)),k5_relat_1('#skF_17','#skF_16'))
      | ~ r2_hidden(C_180,k1_relat_1(k5_relat_1('#skF_17','#skF_16'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_127])).

tff(c_146,plain,(
    ! [C_180] :
      ( r2_hidden(k4_tarski(C_180,'#skF_5'(k5_relat_1('#skF_17','#skF_16'),k1_relat_1('#skF_17'),C_180)),k5_relat_1('#skF_17','#skF_16'))
      | ~ r2_hidden(C_180,k1_relat_1('#skF_17')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_141])).

tff(c_1141,plain,(
    ! [E_347,B_348,D_349,A_350] :
      ( r2_hidden(k4_tarski('#skF_10'(E_347,B_348,D_349,A_350,k5_relat_1(A_350,B_348)),E_347),B_348)
      | ~ r2_hidden(k4_tarski(D_349,E_347),k5_relat_1(A_350,B_348))
      | ~ v1_relat_1(k5_relat_1(A_350,B_348))
      | ~ v1_relat_1(B_348)
      | ~ v1_relat_1(A_350) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_22,plain,(
    ! [C_40,A_25,D_43] :
      ( r2_hidden(C_40,k2_relat_1(A_25))
      | ~ r2_hidden(k4_tarski(D_43,C_40),A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_1507,plain,(
    ! [E_369,B_370,D_371,A_372] :
      ( r2_hidden(E_369,k2_relat_1(B_370))
      | ~ r2_hidden(k4_tarski(D_371,E_369),k5_relat_1(A_372,B_370))
      | ~ v1_relat_1(k5_relat_1(A_372,B_370))
      | ~ v1_relat_1(B_370)
      | ~ v1_relat_1(A_372) ) ),
    inference(resolution,[status(thm)],[c_1141,c_22])).

tff(c_1530,plain,(
    ! [C_180] :
      ( r2_hidden('#skF_5'(k5_relat_1('#skF_17','#skF_16'),k1_relat_1('#skF_17'),C_180),k2_relat_1('#skF_16'))
      | ~ v1_relat_1(k5_relat_1('#skF_17','#skF_16'))
      | ~ v1_relat_1('#skF_16')
      | ~ v1_relat_1('#skF_17')
      | ~ r2_hidden(C_180,k1_relat_1('#skF_17')) ) ),
    inference(resolution,[status(thm)],[c_146,c_1507])).

tff(c_1566,plain,(
    ! [C_180] :
      ( r2_hidden('#skF_5'(k5_relat_1('#skF_17','#skF_16'),k1_relat_1('#skF_17'),C_180),k2_relat_1('#skF_16'))
      | ~ v1_relat_1(k5_relat_1('#skF_17','#skF_16'))
      | ~ r2_hidden(C_180,k1_relat_1('#skF_17')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_68,c_1530])).

tff(c_1574,plain,(
    ~ v1_relat_1(k5_relat_1('#skF_17','#skF_16')) ),
    inference(splitLeft,[status(thm)],[c_1566])).

tff(c_1577,plain,
    ( ~ v1_relat_1('#skF_16')
    | ~ v1_relat_1('#skF_17') ),
    inference(resolution,[status(thm)],[c_50,c_1574])).

tff(c_1581,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_68,c_1577])).

tff(c_1583,plain,(
    v1_relat_1(k5_relat_1('#skF_17','#skF_16')) ),
    inference(splitRight,[status(thm)],[c_1566])).

tff(c_968,plain,(
    ! [D_314,E_315,B_316,A_317] :
      ( r2_hidden(k4_tarski(D_314,'#skF_10'(E_315,B_316,D_314,A_317,k5_relat_1(A_317,B_316))),A_317)
      | ~ r2_hidden(k4_tarski(D_314,E_315),k5_relat_1(A_317,B_316))
      | ~ v1_relat_1(k5_relat_1(A_317,B_316))
      | ~ v1_relat_1(B_316)
      | ~ v1_relat_1(A_317) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_54,plain,(
    ! [C_147,A_145,B_146] :
      ( k1_funct_1(C_147,A_145) = B_146
      | ~ r2_hidden(k4_tarski(A_145,B_146),C_147)
      | ~ v1_funct_1(C_147)
      | ~ v1_relat_1(C_147) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_7728,plain,(
    ! [E_658,B_659,D_660,A_661] :
      ( '#skF_10'(E_658,B_659,D_660,A_661,k5_relat_1(A_661,B_659)) = k1_funct_1(A_661,D_660)
      | ~ v1_funct_1(A_661)
      | ~ r2_hidden(k4_tarski(D_660,E_658),k5_relat_1(A_661,B_659))
      | ~ v1_relat_1(k5_relat_1(A_661,B_659))
      | ~ v1_relat_1(B_659)
      | ~ v1_relat_1(A_661) ) ),
    inference(resolution,[status(thm)],[c_968,c_54])).

tff(c_7771,plain,(
    ! [C_180] :
      ( '#skF_10'('#skF_5'(k5_relat_1('#skF_17','#skF_16'),k1_relat_1('#skF_17'),C_180),'#skF_16',C_180,'#skF_17',k5_relat_1('#skF_17','#skF_16')) = k1_funct_1('#skF_17',C_180)
      | ~ v1_funct_1('#skF_17')
      | ~ v1_relat_1(k5_relat_1('#skF_17','#skF_16'))
      | ~ v1_relat_1('#skF_16')
      | ~ v1_relat_1('#skF_17')
      | ~ r2_hidden(C_180,k1_relat_1('#skF_17')) ) ),
    inference(resolution,[status(thm)],[c_146,c_7728])).

tff(c_8415,plain,(
    ! [C_704] :
      ( '#skF_10'('#skF_5'(k5_relat_1('#skF_17','#skF_16'),k1_relat_1('#skF_17'),C_704),'#skF_16',C_704,'#skF_17',k5_relat_1('#skF_17','#skF_16')) = k1_funct_1('#skF_17',C_704)
      | ~ r2_hidden(C_704,k1_relat_1('#skF_17')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_68,c_1583,c_62,c_7771])).

tff(c_1165,plain,(
    ! [E_347,B_348,D_349,A_350] :
      ( r2_hidden('#skF_10'(E_347,B_348,D_349,A_350,k5_relat_1(A_350,B_348)),k1_relat_1(B_348))
      | ~ r2_hidden(k4_tarski(D_349,E_347),k5_relat_1(A_350,B_348))
      | ~ v1_relat_1(k5_relat_1(A_350,B_348))
      | ~ v1_relat_1(B_348)
      | ~ v1_relat_1(A_350) ) ),
    inference(resolution,[status(thm)],[c_1141,c_10])).

tff(c_8424,plain,(
    ! [C_704] :
      ( r2_hidden(k1_funct_1('#skF_17',C_704),k1_relat_1('#skF_16'))
      | ~ r2_hidden(k4_tarski(C_704,'#skF_5'(k5_relat_1('#skF_17','#skF_16'),k1_relat_1('#skF_17'),C_704)),k5_relat_1('#skF_17','#skF_16'))
      | ~ v1_relat_1(k5_relat_1('#skF_17','#skF_16'))
      | ~ v1_relat_1('#skF_16')
      | ~ v1_relat_1('#skF_17')
      | ~ r2_hidden(C_704,k1_relat_1('#skF_17')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8415,c_1165])).

tff(c_25230,plain,(
    ! [C_1151] :
      ( r2_hidden(k1_funct_1('#skF_17',C_1151),k1_relat_1('#skF_16'))
      | ~ r2_hidden(k4_tarski(C_1151,'#skF_5'(k5_relat_1('#skF_17','#skF_16'),k1_relat_1('#skF_17'),C_1151)),k5_relat_1('#skF_17','#skF_16'))
      | ~ r2_hidden(C_1151,k1_relat_1('#skF_17')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_68,c_1583,c_8424])).

tff(c_25234,plain,(
    ! [C_207] :
      ( r2_hidden(k1_funct_1('#skF_17',C_207),k1_relat_1('#skF_16'))
      | ~ r1_tarski(k5_relat_1('#skF_17','#skF_16'),k5_relat_1('#skF_17','#skF_16'))
      | ~ r2_hidden(C_207,k1_relat_1('#skF_17')) ) ),
    inference(resolution,[status(thm)],[c_261,c_25230])).

tff(c_25242,plain,(
    ! [C_1152] :
      ( r2_hidden(k1_funct_1('#skF_17',C_1152),k1_relat_1('#skF_16'))
      | ~ r2_hidden(C_1152,k1_relat_1('#skF_17')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_25234])).

tff(c_25266,plain,(
    ! [C_40] :
      ( r2_hidden(C_40,k1_relat_1('#skF_16'))
      | ~ r2_hidden('#skF_9'('#skF_17',k2_relat_1('#skF_17'),C_40),k1_relat_1('#skF_17'))
      | ~ v1_funct_1('#skF_17')
      | ~ v1_relat_1('#skF_17')
      | ~ r2_hidden(C_40,k2_relat_1('#skF_17')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_121,c_25242])).

tff(c_25387,plain,(
    ! [C_1155] :
      ( r2_hidden(C_1155,k1_relat_1('#skF_16'))
      | ~ r2_hidden('#skF_9'('#skF_17',k2_relat_1('#skF_17'),C_1155),k1_relat_1('#skF_17'))
      | ~ r2_hidden(C_1155,k2_relat_1('#skF_17')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_25266])).

tff(c_25444,plain,(
    ! [C_1156] :
      ( r2_hidden(C_1156,k1_relat_1('#skF_16'))
      | ~ r2_hidden(C_1156,k2_relat_1('#skF_17')) ) ),
    inference(resolution,[status(thm)],[c_107,c_25387])).

tff(c_26207,plain,(
    ! [B_1157] :
      ( r2_hidden('#skF_1'(k2_relat_1('#skF_17'),B_1157),k1_relat_1('#skF_16'))
      | r1_tarski(k2_relat_1('#skF_17'),B_1157) ) ),
    inference(resolution,[status(thm)],[c_6,c_25444])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_26215,plain,(
    r1_tarski(k2_relat_1('#skF_17'),k1_relat_1('#skF_16')) ),
    inference(resolution,[status(thm)],[c_26207,c_4])).

tff(c_26223,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_58,c_26215])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n017.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 20:41:16 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 14.33/6.90  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 14.33/6.91  
% 14.33/6.91  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 14.33/6.91  %$ r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k5_relat_1 > k4_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_13 > #skF_6 > #skF_17 > #skF_12 > #skF_3 > #skF_16 > #skF_5 > #skF_8 > #skF_10 > #skF_11 > #skF_9 > #skF_15 > #skF_14 > #skF_2 > #skF_7 > #skF_1 > #skF_4
% 14.33/6.91  
% 14.33/6.91  %Foreground sorts:
% 14.33/6.91  
% 14.33/6.91  
% 14.33/6.91  %Background operators:
% 14.33/6.91  
% 14.33/6.91  
% 14.33/6.91  %Foreground operators:
% 14.33/6.91  tff('#skF_13', type, '#skF_13': ($i * $i * $i) > $i).
% 14.33/6.91  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 14.33/6.91  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 14.33/6.91  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 14.33/6.91  tff('#skF_17', type, '#skF_17': $i).
% 14.33/6.91  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 14.33/6.91  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 14.33/6.91  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 14.33/6.91  tff('#skF_12', type, '#skF_12': ($i * $i * $i) > $i).
% 14.33/6.91  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 14.33/6.91  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 14.33/6.91  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 14.33/6.91  tff('#skF_16', type, '#skF_16': $i).
% 14.33/6.91  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 14.33/6.91  tff('#skF_8', type, '#skF_8': ($i * $i) > $i).
% 14.33/6.91  tff('#skF_10', type, '#skF_10': ($i * $i * $i * $i * $i) > $i).
% 14.33/6.91  tff('#skF_11', type, '#skF_11': ($i * $i * $i) > $i).
% 14.33/6.91  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 14.33/6.91  tff('#skF_9', type, '#skF_9': ($i * $i * $i) > $i).
% 14.33/6.91  tff('#skF_15', type, '#skF_15': ($i * $i * $i) > $i).
% 14.33/6.91  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 14.33/6.91  tff('#skF_14', type, '#skF_14': ($i * $i * $i) > $i).
% 14.33/6.91  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 14.33/6.91  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 14.33/6.91  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 14.33/6.91  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 14.33/6.91  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 14.33/6.91  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 14.33/6.91  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 14.33/6.91  
% 14.33/6.93  tff(f_96, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(k5_relat_1(B, A)) = k1_relat_1(B)) => r1_tarski(k2_relat_1(B), k1_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t27_funct_1)).
% 14.33/6.93  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 14.33/6.93  tff(f_48, axiom, (![A, B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(D, C), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_relat_1)).
% 14.33/6.93  tff(f_40, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_relat_1)).
% 14.33/6.93  tff(f_82, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(k4_tarski(A, B), C) <=> (r2_hidden(A, k1_relat_1(C)) & (B = k1_funct_1(C, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_funct_1)).
% 14.33/6.93  tff(f_72, axiom, (![A, B]: ((v1_relat_1(A) & v1_relat_1(B)) => v1_relat_1(k5_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 14.33/6.93  tff(f_66, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => ((C = k5_relat_1(A, B)) <=> (![D, E]: (r2_hidden(k4_tarski(D, E), C) <=> (?[F]: (r2_hidden(k4_tarski(D, F), A) & r2_hidden(k4_tarski(F, E), B)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_relat_1)).
% 14.33/6.93  tff(c_58, plain, (~r1_tarski(k2_relat_1('#skF_17'), k1_relat_1('#skF_16'))), inference(cnfTransformation, [status(thm)], [f_96])).
% 14.33/6.93  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 14.33/6.93  tff(c_98, plain, (![A_170, C_171]: (r2_hidden(k4_tarski('#skF_9'(A_170, k2_relat_1(A_170), C_171), C_171), A_170) | ~r2_hidden(C_171, k2_relat_1(A_170)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 14.33/6.93  tff(c_10, plain, (![C_21, A_6, D_24]: (r2_hidden(C_21, k1_relat_1(A_6)) | ~r2_hidden(k4_tarski(C_21, D_24), A_6))), inference(cnfTransformation, [status(thm)], [f_40])).
% 14.33/6.93  tff(c_107, plain, (![A_170, C_171]: (r2_hidden('#skF_9'(A_170, k2_relat_1(A_170), C_171), k1_relat_1(A_170)) | ~r2_hidden(C_171, k2_relat_1(A_170)))), inference(resolution, [status(thm)], [c_98, c_10])).
% 14.33/6.93  tff(c_64, plain, (v1_relat_1('#skF_17')), inference(cnfTransformation, [status(thm)], [f_96])).
% 14.33/6.93  tff(c_62, plain, (v1_funct_1('#skF_17')), inference(cnfTransformation, [status(thm)], [f_96])).
% 14.33/6.93  tff(c_20, plain, (![A_25, C_40]: (r2_hidden(k4_tarski('#skF_9'(A_25, k2_relat_1(A_25), C_40), C_40), A_25) | ~r2_hidden(C_40, k2_relat_1(A_25)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 14.33/6.93  tff(c_117, plain, (![C_174, A_175, B_176]: (k1_funct_1(C_174, A_175)=B_176 | ~r2_hidden(k4_tarski(A_175, B_176), C_174) | ~v1_funct_1(C_174) | ~v1_relat_1(C_174))), inference(cnfTransformation, [status(thm)], [f_82])).
% 14.33/6.93  tff(c_121, plain, (![A_25, C_40]: (k1_funct_1(A_25, '#skF_9'(A_25, k2_relat_1(A_25), C_40))=C_40 | ~v1_funct_1(A_25) | ~v1_relat_1(A_25) | ~r2_hidden(C_40, k2_relat_1(A_25)))), inference(resolution, [status(thm)], [c_20, c_117])).
% 14.33/6.93  tff(c_75, plain, (![A_153, B_154]: (~r2_hidden('#skF_1'(A_153, B_154), B_154) | r1_tarski(A_153, B_154))), inference(cnfTransformation, [status(thm)], [f_32])).
% 14.33/6.93  tff(c_80, plain, (![A_1]: (r1_tarski(A_1, A_1))), inference(resolution, [status(thm)], [c_6, c_75])).
% 14.33/6.93  tff(c_60, plain, (k1_relat_1(k5_relat_1('#skF_17', '#skF_16'))=k1_relat_1('#skF_17')), inference(cnfTransformation, [status(thm)], [f_96])).
% 14.33/6.93  tff(c_127, plain, (![C_180, A_181]: (r2_hidden(k4_tarski(C_180, '#skF_5'(A_181, k1_relat_1(A_181), C_180)), A_181) | ~r2_hidden(C_180, k1_relat_1(A_181)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 14.33/6.93  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 14.33/6.93  tff(c_238, plain, (![C_207, A_208, B_209]: (r2_hidden(k4_tarski(C_207, '#skF_5'(A_208, k1_relat_1(A_208), C_207)), B_209) | ~r1_tarski(A_208, B_209) | ~r2_hidden(C_207, k1_relat_1(A_208)))), inference(resolution, [status(thm)], [c_127, c_2])).
% 14.33/6.93  tff(c_255, plain, (![C_207, B_209]: (r2_hidden(k4_tarski(C_207, '#skF_5'(k5_relat_1('#skF_17', '#skF_16'), k1_relat_1('#skF_17'), C_207)), B_209) | ~r1_tarski(k5_relat_1('#skF_17', '#skF_16'), B_209) | ~r2_hidden(C_207, k1_relat_1(k5_relat_1('#skF_17', '#skF_16'))))), inference(superposition, [status(thm), theory('equality')], [c_60, c_238])).
% 14.33/6.93  tff(c_261, plain, (![C_207, B_209]: (r2_hidden(k4_tarski(C_207, '#skF_5'(k5_relat_1('#skF_17', '#skF_16'), k1_relat_1('#skF_17'), C_207)), B_209) | ~r1_tarski(k5_relat_1('#skF_17', '#skF_16'), B_209) | ~r2_hidden(C_207, k1_relat_1('#skF_17')))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_255])).
% 14.33/6.93  tff(c_68, plain, (v1_relat_1('#skF_16')), inference(cnfTransformation, [status(thm)], [f_96])).
% 14.33/6.93  tff(c_50, plain, (![A_143, B_144]: (v1_relat_1(k5_relat_1(A_143, B_144)) | ~v1_relat_1(B_144) | ~v1_relat_1(A_143))), inference(cnfTransformation, [status(thm)], [f_72])).
% 14.33/6.93  tff(c_141, plain, (![C_180]: (r2_hidden(k4_tarski(C_180, '#skF_5'(k5_relat_1('#skF_17', '#skF_16'), k1_relat_1('#skF_17'), C_180)), k5_relat_1('#skF_17', '#skF_16')) | ~r2_hidden(C_180, k1_relat_1(k5_relat_1('#skF_17', '#skF_16'))))), inference(superposition, [status(thm), theory('equality')], [c_60, c_127])).
% 14.33/6.93  tff(c_146, plain, (![C_180]: (r2_hidden(k4_tarski(C_180, '#skF_5'(k5_relat_1('#skF_17', '#skF_16'), k1_relat_1('#skF_17'), C_180)), k5_relat_1('#skF_17', '#skF_16')) | ~r2_hidden(C_180, k1_relat_1('#skF_17')))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_141])).
% 14.33/6.93  tff(c_1141, plain, (![E_347, B_348, D_349, A_350]: (r2_hidden(k4_tarski('#skF_10'(E_347, B_348, D_349, A_350, k5_relat_1(A_350, B_348)), E_347), B_348) | ~r2_hidden(k4_tarski(D_349, E_347), k5_relat_1(A_350, B_348)) | ~v1_relat_1(k5_relat_1(A_350, B_348)) | ~v1_relat_1(B_348) | ~v1_relat_1(A_350))), inference(cnfTransformation, [status(thm)], [f_66])).
% 14.33/6.93  tff(c_22, plain, (![C_40, A_25, D_43]: (r2_hidden(C_40, k2_relat_1(A_25)) | ~r2_hidden(k4_tarski(D_43, C_40), A_25))), inference(cnfTransformation, [status(thm)], [f_48])).
% 14.33/6.93  tff(c_1507, plain, (![E_369, B_370, D_371, A_372]: (r2_hidden(E_369, k2_relat_1(B_370)) | ~r2_hidden(k4_tarski(D_371, E_369), k5_relat_1(A_372, B_370)) | ~v1_relat_1(k5_relat_1(A_372, B_370)) | ~v1_relat_1(B_370) | ~v1_relat_1(A_372))), inference(resolution, [status(thm)], [c_1141, c_22])).
% 14.33/6.93  tff(c_1530, plain, (![C_180]: (r2_hidden('#skF_5'(k5_relat_1('#skF_17', '#skF_16'), k1_relat_1('#skF_17'), C_180), k2_relat_1('#skF_16')) | ~v1_relat_1(k5_relat_1('#skF_17', '#skF_16')) | ~v1_relat_1('#skF_16') | ~v1_relat_1('#skF_17') | ~r2_hidden(C_180, k1_relat_1('#skF_17')))), inference(resolution, [status(thm)], [c_146, c_1507])).
% 14.33/6.93  tff(c_1566, plain, (![C_180]: (r2_hidden('#skF_5'(k5_relat_1('#skF_17', '#skF_16'), k1_relat_1('#skF_17'), C_180), k2_relat_1('#skF_16')) | ~v1_relat_1(k5_relat_1('#skF_17', '#skF_16')) | ~r2_hidden(C_180, k1_relat_1('#skF_17')))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_68, c_1530])).
% 14.33/6.93  tff(c_1574, plain, (~v1_relat_1(k5_relat_1('#skF_17', '#skF_16'))), inference(splitLeft, [status(thm)], [c_1566])).
% 14.33/6.93  tff(c_1577, plain, (~v1_relat_1('#skF_16') | ~v1_relat_1('#skF_17')), inference(resolution, [status(thm)], [c_50, c_1574])).
% 14.33/6.93  tff(c_1581, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_64, c_68, c_1577])).
% 14.33/6.93  tff(c_1583, plain, (v1_relat_1(k5_relat_1('#skF_17', '#skF_16'))), inference(splitRight, [status(thm)], [c_1566])).
% 14.33/6.93  tff(c_968, plain, (![D_314, E_315, B_316, A_317]: (r2_hidden(k4_tarski(D_314, '#skF_10'(E_315, B_316, D_314, A_317, k5_relat_1(A_317, B_316))), A_317) | ~r2_hidden(k4_tarski(D_314, E_315), k5_relat_1(A_317, B_316)) | ~v1_relat_1(k5_relat_1(A_317, B_316)) | ~v1_relat_1(B_316) | ~v1_relat_1(A_317))), inference(cnfTransformation, [status(thm)], [f_66])).
% 14.33/6.93  tff(c_54, plain, (![C_147, A_145, B_146]: (k1_funct_1(C_147, A_145)=B_146 | ~r2_hidden(k4_tarski(A_145, B_146), C_147) | ~v1_funct_1(C_147) | ~v1_relat_1(C_147))), inference(cnfTransformation, [status(thm)], [f_82])).
% 14.33/6.93  tff(c_7728, plain, (![E_658, B_659, D_660, A_661]: ('#skF_10'(E_658, B_659, D_660, A_661, k5_relat_1(A_661, B_659))=k1_funct_1(A_661, D_660) | ~v1_funct_1(A_661) | ~r2_hidden(k4_tarski(D_660, E_658), k5_relat_1(A_661, B_659)) | ~v1_relat_1(k5_relat_1(A_661, B_659)) | ~v1_relat_1(B_659) | ~v1_relat_1(A_661))), inference(resolution, [status(thm)], [c_968, c_54])).
% 14.33/6.93  tff(c_7771, plain, (![C_180]: ('#skF_10'('#skF_5'(k5_relat_1('#skF_17', '#skF_16'), k1_relat_1('#skF_17'), C_180), '#skF_16', C_180, '#skF_17', k5_relat_1('#skF_17', '#skF_16'))=k1_funct_1('#skF_17', C_180) | ~v1_funct_1('#skF_17') | ~v1_relat_1(k5_relat_1('#skF_17', '#skF_16')) | ~v1_relat_1('#skF_16') | ~v1_relat_1('#skF_17') | ~r2_hidden(C_180, k1_relat_1('#skF_17')))), inference(resolution, [status(thm)], [c_146, c_7728])).
% 14.33/6.93  tff(c_8415, plain, (![C_704]: ('#skF_10'('#skF_5'(k5_relat_1('#skF_17', '#skF_16'), k1_relat_1('#skF_17'), C_704), '#skF_16', C_704, '#skF_17', k5_relat_1('#skF_17', '#skF_16'))=k1_funct_1('#skF_17', C_704) | ~r2_hidden(C_704, k1_relat_1('#skF_17')))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_68, c_1583, c_62, c_7771])).
% 14.33/6.93  tff(c_1165, plain, (![E_347, B_348, D_349, A_350]: (r2_hidden('#skF_10'(E_347, B_348, D_349, A_350, k5_relat_1(A_350, B_348)), k1_relat_1(B_348)) | ~r2_hidden(k4_tarski(D_349, E_347), k5_relat_1(A_350, B_348)) | ~v1_relat_1(k5_relat_1(A_350, B_348)) | ~v1_relat_1(B_348) | ~v1_relat_1(A_350))), inference(resolution, [status(thm)], [c_1141, c_10])).
% 14.33/6.93  tff(c_8424, plain, (![C_704]: (r2_hidden(k1_funct_1('#skF_17', C_704), k1_relat_1('#skF_16')) | ~r2_hidden(k4_tarski(C_704, '#skF_5'(k5_relat_1('#skF_17', '#skF_16'), k1_relat_1('#skF_17'), C_704)), k5_relat_1('#skF_17', '#skF_16')) | ~v1_relat_1(k5_relat_1('#skF_17', '#skF_16')) | ~v1_relat_1('#skF_16') | ~v1_relat_1('#skF_17') | ~r2_hidden(C_704, k1_relat_1('#skF_17')))), inference(superposition, [status(thm), theory('equality')], [c_8415, c_1165])).
% 14.33/6.93  tff(c_25230, plain, (![C_1151]: (r2_hidden(k1_funct_1('#skF_17', C_1151), k1_relat_1('#skF_16')) | ~r2_hidden(k4_tarski(C_1151, '#skF_5'(k5_relat_1('#skF_17', '#skF_16'), k1_relat_1('#skF_17'), C_1151)), k5_relat_1('#skF_17', '#skF_16')) | ~r2_hidden(C_1151, k1_relat_1('#skF_17')))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_68, c_1583, c_8424])).
% 14.33/6.93  tff(c_25234, plain, (![C_207]: (r2_hidden(k1_funct_1('#skF_17', C_207), k1_relat_1('#skF_16')) | ~r1_tarski(k5_relat_1('#skF_17', '#skF_16'), k5_relat_1('#skF_17', '#skF_16')) | ~r2_hidden(C_207, k1_relat_1('#skF_17')))), inference(resolution, [status(thm)], [c_261, c_25230])).
% 14.33/6.93  tff(c_25242, plain, (![C_1152]: (r2_hidden(k1_funct_1('#skF_17', C_1152), k1_relat_1('#skF_16')) | ~r2_hidden(C_1152, k1_relat_1('#skF_17')))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_25234])).
% 14.33/6.93  tff(c_25266, plain, (![C_40]: (r2_hidden(C_40, k1_relat_1('#skF_16')) | ~r2_hidden('#skF_9'('#skF_17', k2_relat_1('#skF_17'), C_40), k1_relat_1('#skF_17')) | ~v1_funct_1('#skF_17') | ~v1_relat_1('#skF_17') | ~r2_hidden(C_40, k2_relat_1('#skF_17')))), inference(superposition, [status(thm), theory('equality')], [c_121, c_25242])).
% 14.33/6.93  tff(c_25387, plain, (![C_1155]: (r2_hidden(C_1155, k1_relat_1('#skF_16')) | ~r2_hidden('#skF_9'('#skF_17', k2_relat_1('#skF_17'), C_1155), k1_relat_1('#skF_17')) | ~r2_hidden(C_1155, k2_relat_1('#skF_17')))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_25266])).
% 14.33/6.93  tff(c_25444, plain, (![C_1156]: (r2_hidden(C_1156, k1_relat_1('#skF_16')) | ~r2_hidden(C_1156, k2_relat_1('#skF_17')))), inference(resolution, [status(thm)], [c_107, c_25387])).
% 14.33/6.93  tff(c_26207, plain, (![B_1157]: (r2_hidden('#skF_1'(k2_relat_1('#skF_17'), B_1157), k1_relat_1('#skF_16')) | r1_tarski(k2_relat_1('#skF_17'), B_1157))), inference(resolution, [status(thm)], [c_6, c_25444])).
% 14.33/6.93  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 14.33/6.93  tff(c_26215, plain, (r1_tarski(k2_relat_1('#skF_17'), k1_relat_1('#skF_16'))), inference(resolution, [status(thm)], [c_26207, c_4])).
% 14.33/6.93  tff(c_26223, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_58, c_26215])).
% 14.33/6.93  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 14.33/6.93  
% 14.33/6.93  Inference rules
% 14.33/6.93  ----------------------
% 14.33/6.93  #Ref     : 0
% 14.33/6.93  #Sup     : 6086
% 14.33/6.93  #Fact    : 0
% 14.33/6.93  #Define  : 0
% 14.33/6.93  #Split   : 9
% 14.33/6.93  #Chain   : 0
% 14.33/6.93  #Close   : 0
% 14.33/6.93  
% 14.33/6.93  Ordering : KBO
% 14.33/6.93  
% 14.33/6.93  Simplification rules
% 14.33/6.93  ----------------------
% 14.33/6.93  #Subsume      : 575
% 14.33/6.93  #Demod        : 724
% 14.33/6.93  #Tautology    : 413
% 14.33/6.93  #SimpNegUnit  : 1
% 14.33/6.93  #BackRed      : 0
% 14.33/6.93  
% 14.33/6.93  #Partial instantiations: 0
% 14.33/6.93  #Strategies tried      : 1
% 14.33/6.93  
% 14.33/6.93  Timing (in seconds)
% 14.33/6.93  ----------------------
% 14.33/6.93  Preprocessing        : 0.32
% 14.33/6.93  Parsing              : 0.16
% 14.33/6.93  CNF conversion       : 0.04
% 14.33/6.93  Main loop            : 5.85
% 14.33/6.93  Inferencing          : 1.23
% 14.33/6.93  Reduction            : 0.95
% 14.33/6.93  Demodulation         : 0.58
% 14.33/6.93  BG Simplification    : 0.16
% 14.33/6.93  Subsumption          : 3.07
% 14.33/6.93  Abstraction          : 0.25
% 14.33/6.93  MUC search           : 0.00
% 14.33/6.93  Cooper               : 0.00
% 14.33/6.93  Total                : 6.20
% 14.33/6.93  Index Insertion      : 0.00
% 14.33/6.93  Index Deletion       : 0.00
% 14.33/6.93  Index Matching       : 0.00
% 14.33/6.93  BG Taut test         : 0.00
%------------------------------------------------------------------------------
