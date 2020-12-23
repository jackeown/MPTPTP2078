%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:48 EST 2020

% Result     : Theorem 3.40s
% Output     : CNFRefutation 3.40s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 235 expanded)
%              Number of leaves         :   40 ( 109 expanded)
%              Depth                    :   12
%              Number of atoms          :  172 ( 900 expanded)
%              Number of equality atoms :   37 ( 183 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r3_wellord1 > r2_hidden > r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k7_relat_1 > k4_xboole_0 > k4_tarski > k1_funct_1 > k10_relat_1 > #nlpp > k3_relat_1 > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_11 > #skF_6 > #skF_4 > #skF_7 > #skF_10 > #skF_5 > #skF_9 > #skF_8 > #skF_3 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(r3_wellord1,type,(
    r3_wellord1: ( $i * $i * $i ) > $o )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_relat_1,type,(
    k3_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_120,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => ! [C] :
                ( ( v1_relat_1(C)
                  & v1_funct_1(C) )
               => ( r3_wellord1(A,B,C)
                 => ! [D,E] :
                      ( r2_hidden(k4_tarski(D,E),A)
                     => ( D = E
                        | ( r2_hidden(k4_tarski(k1_funct_1(C,D),k1_funct_1(C,E)),B)
                          & k1_funct_1(C,D) != k1_funct_1(C,E) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_wellord1)).

tff(f_97,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( ( v1_relat_1(C)
                & v1_funct_1(C) )
             => ( r3_wellord1(A,B,C)
              <=> ( k1_relat_1(C) = k3_relat_1(A)
                  & k2_relat_1(C) = k3_relat_1(B)
                  & v2_funct_1(C)
                  & ! [D,E] :
                      ( r2_hidden(k4_tarski(D,E),A)
                    <=> ( r2_hidden(D,k3_relat_1(A))
                        & r2_hidden(E,k3_relat_1(A))
                        & r2_hidden(k4_tarski(k1_funct_1(C,D),k1_funct_1(C,E)),B) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_wellord1)).

tff(f_52,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(k4_tarski(A,B),C)
       => ( r2_hidden(A,k3_relat_1(C))
          & r2_hidden(B,k3_relat_1(C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_relat_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r2_hidden(A,k1_relat_1(B))
       => k2_relat_1(k7_relat_1(B,k1_tarski(A))) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t168_funct_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),B) = k1_xboole_0
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l35_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_xboole_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( ( r1_tarski(A,k1_relat_1(B))
          & v2_funct_1(B) )
       => k10_relat_1(B,k9_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t164_funct_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(c_64,plain,(
    '#skF_11' != '#skF_10' ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_76,plain,(
    v1_relat_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_74,plain,(
    v1_relat_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_72,plain,(
    v1_relat_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_70,plain,(
    v1_funct_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_68,plain,(
    r3_wellord1('#skF_7','#skF_8','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_530,plain,(
    ! [A_178,C_179,B_180] :
      ( k3_relat_1(A_178) = k1_relat_1(C_179)
      | ~ r3_wellord1(A_178,B_180,C_179)
      | ~ v1_funct_1(C_179)
      | ~ v1_relat_1(C_179)
      | ~ v1_relat_1(B_180)
      | ~ v1_relat_1(A_178) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_533,plain,
    ( k3_relat_1('#skF_7') = k1_relat_1('#skF_9')
    | ~ v1_funct_1('#skF_9')
    | ~ v1_relat_1('#skF_9')
    | ~ v1_relat_1('#skF_8')
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_68,c_530])).

tff(c_536,plain,(
    k3_relat_1('#skF_7') = k1_relat_1('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_72,c_70,c_533])).

tff(c_66,plain,(
    r2_hidden(k4_tarski('#skF_10','#skF_11'),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_411,plain,(
    ! [A_150,C_151,B_152] :
      ( r2_hidden(A_150,k3_relat_1(C_151))
      | ~ r2_hidden(k4_tarski(A_150,B_152),C_151)
      | ~ v1_relat_1(C_151) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_417,plain,
    ( r2_hidden('#skF_10',k3_relat_1('#skF_7'))
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_66,c_411])).

tff(c_427,plain,(
    r2_hidden('#skF_10',k3_relat_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_417])).

tff(c_554,plain,(
    r2_hidden('#skF_10',k1_relat_1('#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_536,c_427])).

tff(c_483,plain,(
    ! [C_168,A_169,B_170] :
      ( v2_funct_1(C_168)
      | ~ r3_wellord1(A_169,B_170,C_168)
      | ~ v1_funct_1(C_168)
      | ~ v1_relat_1(C_168)
      | ~ v1_relat_1(B_170)
      | ~ v1_relat_1(A_169) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_486,plain,
    ( v2_funct_1('#skF_9')
    | ~ v1_funct_1('#skF_9')
    | ~ v1_relat_1('#skF_9')
    | ~ v1_relat_1('#skF_8')
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_68,c_483])).

tff(c_489,plain,(
    v2_funct_1('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_72,c_70,c_486])).

tff(c_537,plain,(
    ! [B_181,A_182] :
      ( k2_relat_1(k7_relat_1(B_181,k1_tarski(A_182))) = k1_tarski(k1_funct_1(B_181,A_182))
      | ~ r2_hidden(A_182,k1_relat_1(B_181))
      | ~ v1_funct_1(B_181)
      | ~ v1_relat_1(B_181) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_22,plain,(
    ! [B_11,A_10] :
      ( k2_relat_1(k7_relat_1(B_11,A_10)) = k9_relat_1(B_11,A_10)
      | ~ v1_relat_1(B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_588,plain,(
    ! [B_192,A_193] :
      ( k9_relat_1(B_192,k1_tarski(A_193)) = k1_tarski(k1_funct_1(B_192,A_193))
      | ~ v1_relat_1(B_192)
      | ~ r2_hidden(A_193,k1_relat_1(B_192))
      | ~ v1_funct_1(B_192)
      | ~ v1_relat_1(B_192) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_537,c_22])).

tff(c_591,plain,
    ( k9_relat_1('#skF_9',k1_tarski('#skF_10')) = k1_tarski(k1_funct_1('#skF_9','#skF_10'))
    | ~ v1_funct_1('#skF_9')
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_554,c_588])).

tff(c_605,plain,(
    k9_relat_1('#skF_9',k1_tarski('#skF_10')) = k1_tarski(k1_funct_1('#skF_9','#skF_10')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_591])).

tff(c_20,plain,(
    ! [A_8,B_9] :
      ( k4_xboole_0(k1_tarski(A_8),B_9) = k1_xboole_0
      | ~ r2_hidden(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r1_tarski(A_1,B_2)
      | k4_xboole_0(A_1,B_2) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_525,plain,(
    ! [B_176,A_177] :
      ( k10_relat_1(B_176,k9_relat_1(B_176,A_177)) = A_177
      | ~ v2_funct_1(B_176)
      | ~ r1_tarski(A_177,k1_relat_1(B_176))
      | ~ v1_funct_1(B_176)
      | ~ v1_relat_1(B_176) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_583,plain,(
    ! [B_190,A_191] :
      ( k10_relat_1(B_190,k9_relat_1(B_190,A_191)) = A_191
      | ~ v2_funct_1(B_190)
      | ~ v1_funct_1(B_190)
      | ~ v1_relat_1(B_190)
      | k4_xboole_0(A_191,k1_relat_1(B_190)) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_2,c_525])).

tff(c_823,plain,(
    ! [B_217,A_218] :
      ( k10_relat_1(B_217,k9_relat_1(B_217,k1_tarski(A_218))) = k1_tarski(A_218)
      | ~ v2_funct_1(B_217)
      | ~ v1_funct_1(B_217)
      | ~ v1_relat_1(B_217)
      | ~ r2_hidden(A_218,k1_relat_1(B_217)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_583])).

tff(c_835,plain,
    ( k10_relat_1('#skF_9',k1_tarski(k1_funct_1('#skF_9','#skF_10'))) = k1_tarski('#skF_10')
    | ~ v2_funct_1('#skF_9')
    | ~ v1_funct_1('#skF_9')
    | ~ v1_relat_1('#skF_9')
    | ~ r2_hidden('#skF_10',k1_relat_1('#skF_9')) ),
    inference(superposition,[status(thm),theory(equality)],[c_605,c_823])).

tff(c_841,plain,(
    k10_relat_1('#skF_9',k1_tarski(k1_funct_1('#skF_9','#skF_10'))) = k1_tarski('#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_554,c_72,c_70,c_489,c_835])).

tff(c_429,plain,(
    ! [B_153,C_154,A_155] :
      ( r2_hidden(B_153,k3_relat_1(C_154))
      | ~ r2_hidden(k4_tarski(A_155,B_153),C_154)
      | ~ v1_relat_1(C_154) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_435,plain,
    ( r2_hidden('#skF_11',k3_relat_1('#skF_7'))
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_66,c_429])).

tff(c_445,plain,(
    r2_hidden('#skF_11',k3_relat_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_435])).

tff(c_553,plain,(
    r2_hidden('#skF_11',k1_relat_1('#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_536,c_445])).

tff(c_255,plain,(
    ! [E_127,C_128,A_126,D_125,B_124] :
      ( r2_hidden(k4_tarski(k1_funct_1(C_128,D_125),k1_funct_1(C_128,E_127)),B_124)
      | ~ r2_hidden(k4_tarski(D_125,E_127),A_126)
      | ~ r3_wellord1(A_126,B_124,C_128)
      | ~ v1_funct_1(C_128)
      | ~ v1_relat_1(C_128)
      | ~ v1_relat_1(B_124)
      | ~ v1_relat_1(A_126) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_263,plain,(
    ! [C_128,B_124] :
      ( r2_hidden(k4_tarski(k1_funct_1(C_128,'#skF_10'),k1_funct_1(C_128,'#skF_11')),B_124)
      | ~ r3_wellord1('#skF_7',B_124,C_128)
      | ~ v1_funct_1(C_128)
      | ~ v1_relat_1(C_128)
      | ~ v1_relat_1(B_124)
      | ~ v1_relat_1('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_66,c_255])).

tff(c_344,plain,(
    ! [C_138,B_139] :
      ( r2_hidden(k4_tarski(k1_funct_1(C_138,'#skF_10'),k1_funct_1(C_138,'#skF_11')),B_139)
      | ~ r3_wellord1('#skF_7',B_139,C_138)
      | ~ v1_funct_1(C_138)
      | ~ v1_relat_1(C_138)
      | ~ v1_relat_1(B_139) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_263])).

tff(c_62,plain,
    ( k1_funct_1('#skF_9','#skF_11') = k1_funct_1('#skF_9','#skF_10')
    | ~ r2_hidden(k4_tarski(k1_funct_1('#skF_9','#skF_10'),k1_funct_1('#skF_9','#skF_11')),'#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_84,plain,(
    ~ r2_hidden(k4_tarski(k1_funct_1('#skF_9','#skF_10'),k1_funct_1('#skF_9','#skF_11')),'#skF_8') ),
    inference(splitLeft,[status(thm)],[c_62])).

tff(c_361,plain,
    ( ~ r3_wellord1('#skF_7','#skF_8','#skF_9')
    | ~ v1_funct_1('#skF_9')
    | ~ v1_relat_1('#skF_9')
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_344,c_84])).

tff(c_374,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_70,c_68,c_361])).

tff(c_375,plain,(
    k1_funct_1('#skF_9','#skF_11') = k1_funct_1('#skF_9','#skF_10') ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_594,plain,
    ( k9_relat_1('#skF_9',k1_tarski('#skF_11')) = k1_tarski(k1_funct_1('#skF_9','#skF_11'))
    | ~ v1_funct_1('#skF_9')
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_553,c_588])).

tff(c_608,plain,(
    k9_relat_1('#skF_9',k1_tarski('#skF_11')) = k1_tarski(k1_funct_1('#skF_9','#skF_10')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_375,c_594])).

tff(c_832,plain,
    ( k10_relat_1('#skF_9',k1_tarski(k1_funct_1('#skF_9','#skF_10'))) = k1_tarski('#skF_11')
    | ~ v2_funct_1('#skF_9')
    | ~ v1_funct_1('#skF_9')
    | ~ v1_relat_1('#skF_9')
    | ~ r2_hidden('#skF_11',k1_relat_1('#skF_9')) ),
    inference(superposition,[status(thm),theory(equality)],[c_608,c_823])).

tff(c_839,plain,(
    k10_relat_1('#skF_9',k1_tarski(k1_funct_1('#skF_9','#skF_10'))) = k1_tarski('#skF_11') ),
    inference(demodulation,[status(thm),theory(equality)],[c_553,c_72,c_70,c_489,c_832])).

tff(c_868,plain,(
    k1_tarski('#skF_11') = k1_tarski('#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_841,c_839])).

tff(c_8,plain,(
    ! [C_7] : r2_hidden(C_7,k1_tarski(C_7)) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_907,plain,(
    r2_hidden('#skF_11',k1_tarski('#skF_10')) ),
    inference(superposition,[status(thm),theory(equality)],[c_868,c_8])).

tff(c_6,plain,(
    ! [C_7,A_3] :
      ( C_7 = A_3
      | ~ r2_hidden(C_7,k1_tarski(A_3)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_919,plain,(
    '#skF_11' = '#skF_10' ),
    inference(resolution,[status(thm)],[c_907,c_6])).

tff(c_923,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_919])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n013.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 10:34:54 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.40/1.56  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.40/1.57  
% 3.40/1.57  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.40/1.57  %$ r3_wellord1 > r2_hidden > r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k7_relat_1 > k4_xboole_0 > k4_tarski > k1_funct_1 > k10_relat_1 > #nlpp > k3_relat_1 > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_11 > #skF_6 > #skF_4 > #skF_7 > #skF_10 > #skF_5 > #skF_9 > #skF_8 > #skF_3 > #skF_2 > #skF_1
% 3.40/1.57  
% 3.40/1.57  %Foreground sorts:
% 3.40/1.57  
% 3.40/1.57  
% 3.40/1.57  %Background operators:
% 3.40/1.57  
% 3.40/1.57  
% 3.40/1.57  %Foreground operators:
% 3.40/1.57  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.40/1.57  tff(r3_wellord1, type, r3_wellord1: ($i * $i * $i) > $o).
% 3.40/1.57  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 3.40/1.57  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.40/1.57  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.40/1.57  tff('#skF_11', type, '#skF_11': $i).
% 3.40/1.57  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 3.40/1.57  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.40/1.57  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.40/1.57  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.40/1.57  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.40/1.57  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.40/1.57  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 3.40/1.57  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 3.40/1.57  tff('#skF_7', type, '#skF_7': $i).
% 3.40/1.57  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.40/1.57  tff('#skF_10', type, '#skF_10': $i).
% 3.40/1.57  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.40/1.57  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 3.40/1.57  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.40/1.57  tff('#skF_9', type, '#skF_9': $i).
% 3.40/1.57  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.40/1.57  tff('#skF_8', type, '#skF_8': $i).
% 3.40/1.57  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.40/1.57  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 3.40/1.57  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.40/1.57  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 3.40/1.57  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.40/1.57  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.40/1.57  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.40/1.57  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.40/1.57  
% 3.40/1.58  tff(f_120, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r3_wellord1(A, B, C) => (![D, E]: (r2_hidden(k4_tarski(D, E), A) => ((D = E) | (r2_hidden(k4_tarski(k1_funct_1(C, D), k1_funct_1(C, E)), B) & ~(k1_funct_1(C, D) = k1_funct_1(C, E))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_wellord1)).
% 3.40/1.58  tff(f_97, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r3_wellord1(A, B, C) <=> ((((k1_relat_1(C) = k3_relat_1(A)) & (k2_relat_1(C) = k3_relat_1(B))) & v2_funct_1(C)) & (![D, E]: (r2_hidden(k4_tarski(D, E), A) <=> ((r2_hidden(D, k3_relat_1(A)) & r2_hidden(E, k3_relat_1(A))) & r2_hidden(k4_tarski(k1_funct_1(C, D), k1_funct_1(C, E)), B)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_wellord1)).
% 3.40/1.58  tff(f_52, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(k4_tarski(A, B), C) => (r2_hidden(A, k3_relat_1(C)) & r2_hidden(B, k3_relat_1(C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t30_relat_1)).
% 3.40/1.58  tff(f_70, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r2_hidden(A, k1_relat_1(B)) => (k2_relat_1(k7_relat_1(B, k1_tarski(A))) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t168_funct_1)).
% 3.40/1.58  tff(f_44, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 3.40/1.58  tff(f_40, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_xboole_0) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l35_zfmisc_1)).
% 3.40/1.58  tff(f_29, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t37_xboole_1)).
% 3.40/1.58  tff(f_62, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((r1_tarski(A, k1_relat_1(B)) & v2_funct_1(B)) => (k10_relat_1(B, k9_relat_1(B, A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t164_funct_1)).
% 3.40/1.58  tff(f_36, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 3.40/1.58  tff(c_64, plain, ('#skF_11'!='#skF_10'), inference(cnfTransformation, [status(thm)], [f_120])).
% 3.40/1.58  tff(c_76, plain, (v1_relat_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_120])).
% 3.40/1.58  tff(c_74, plain, (v1_relat_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_120])).
% 3.40/1.58  tff(c_72, plain, (v1_relat_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_120])).
% 3.40/1.58  tff(c_70, plain, (v1_funct_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_120])).
% 3.40/1.58  tff(c_68, plain, (r3_wellord1('#skF_7', '#skF_8', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_120])).
% 3.40/1.58  tff(c_530, plain, (![A_178, C_179, B_180]: (k3_relat_1(A_178)=k1_relat_1(C_179) | ~r3_wellord1(A_178, B_180, C_179) | ~v1_funct_1(C_179) | ~v1_relat_1(C_179) | ~v1_relat_1(B_180) | ~v1_relat_1(A_178))), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.40/1.58  tff(c_533, plain, (k3_relat_1('#skF_7')=k1_relat_1('#skF_9') | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9') | ~v1_relat_1('#skF_8') | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_68, c_530])).
% 3.40/1.58  tff(c_536, plain, (k3_relat_1('#skF_7')=k1_relat_1('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_72, c_70, c_533])).
% 3.40/1.58  tff(c_66, plain, (r2_hidden(k4_tarski('#skF_10', '#skF_11'), '#skF_7')), inference(cnfTransformation, [status(thm)], [f_120])).
% 3.40/1.58  tff(c_411, plain, (![A_150, C_151, B_152]: (r2_hidden(A_150, k3_relat_1(C_151)) | ~r2_hidden(k4_tarski(A_150, B_152), C_151) | ~v1_relat_1(C_151))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.40/1.58  tff(c_417, plain, (r2_hidden('#skF_10', k3_relat_1('#skF_7')) | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_66, c_411])).
% 3.40/1.58  tff(c_427, plain, (r2_hidden('#skF_10', k3_relat_1('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_417])).
% 3.40/1.58  tff(c_554, plain, (r2_hidden('#skF_10', k1_relat_1('#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_536, c_427])).
% 3.40/1.58  tff(c_483, plain, (![C_168, A_169, B_170]: (v2_funct_1(C_168) | ~r3_wellord1(A_169, B_170, C_168) | ~v1_funct_1(C_168) | ~v1_relat_1(C_168) | ~v1_relat_1(B_170) | ~v1_relat_1(A_169))), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.40/1.58  tff(c_486, plain, (v2_funct_1('#skF_9') | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9') | ~v1_relat_1('#skF_8') | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_68, c_483])).
% 3.40/1.58  tff(c_489, plain, (v2_funct_1('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_72, c_70, c_486])).
% 3.40/1.58  tff(c_537, plain, (![B_181, A_182]: (k2_relat_1(k7_relat_1(B_181, k1_tarski(A_182)))=k1_tarski(k1_funct_1(B_181, A_182)) | ~r2_hidden(A_182, k1_relat_1(B_181)) | ~v1_funct_1(B_181) | ~v1_relat_1(B_181))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.40/1.58  tff(c_22, plain, (![B_11, A_10]: (k2_relat_1(k7_relat_1(B_11, A_10))=k9_relat_1(B_11, A_10) | ~v1_relat_1(B_11))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.40/1.58  tff(c_588, plain, (![B_192, A_193]: (k9_relat_1(B_192, k1_tarski(A_193))=k1_tarski(k1_funct_1(B_192, A_193)) | ~v1_relat_1(B_192) | ~r2_hidden(A_193, k1_relat_1(B_192)) | ~v1_funct_1(B_192) | ~v1_relat_1(B_192))), inference(superposition, [status(thm), theory('equality')], [c_537, c_22])).
% 3.40/1.58  tff(c_591, plain, (k9_relat_1('#skF_9', k1_tarski('#skF_10'))=k1_tarski(k1_funct_1('#skF_9', '#skF_10')) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_554, c_588])).
% 3.40/1.58  tff(c_605, plain, (k9_relat_1('#skF_9', k1_tarski('#skF_10'))=k1_tarski(k1_funct_1('#skF_9', '#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_591])).
% 3.40/1.58  tff(c_20, plain, (![A_8, B_9]: (k4_xboole_0(k1_tarski(A_8), B_9)=k1_xboole_0 | ~r2_hidden(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.40/1.58  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(A_1, B_2) | k4_xboole_0(A_1, B_2)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.40/1.58  tff(c_525, plain, (![B_176, A_177]: (k10_relat_1(B_176, k9_relat_1(B_176, A_177))=A_177 | ~v2_funct_1(B_176) | ~r1_tarski(A_177, k1_relat_1(B_176)) | ~v1_funct_1(B_176) | ~v1_relat_1(B_176))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.40/1.58  tff(c_583, plain, (![B_190, A_191]: (k10_relat_1(B_190, k9_relat_1(B_190, A_191))=A_191 | ~v2_funct_1(B_190) | ~v1_funct_1(B_190) | ~v1_relat_1(B_190) | k4_xboole_0(A_191, k1_relat_1(B_190))!=k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_525])).
% 3.40/1.58  tff(c_823, plain, (![B_217, A_218]: (k10_relat_1(B_217, k9_relat_1(B_217, k1_tarski(A_218)))=k1_tarski(A_218) | ~v2_funct_1(B_217) | ~v1_funct_1(B_217) | ~v1_relat_1(B_217) | ~r2_hidden(A_218, k1_relat_1(B_217)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_583])).
% 3.40/1.58  tff(c_835, plain, (k10_relat_1('#skF_9', k1_tarski(k1_funct_1('#skF_9', '#skF_10')))=k1_tarski('#skF_10') | ~v2_funct_1('#skF_9') | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9') | ~r2_hidden('#skF_10', k1_relat_1('#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_605, c_823])).
% 3.40/1.58  tff(c_841, plain, (k10_relat_1('#skF_9', k1_tarski(k1_funct_1('#skF_9', '#skF_10')))=k1_tarski('#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_554, c_72, c_70, c_489, c_835])).
% 3.40/1.58  tff(c_429, plain, (![B_153, C_154, A_155]: (r2_hidden(B_153, k3_relat_1(C_154)) | ~r2_hidden(k4_tarski(A_155, B_153), C_154) | ~v1_relat_1(C_154))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.40/1.58  tff(c_435, plain, (r2_hidden('#skF_11', k3_relat_1('#skF_7')) | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_66, c_429])).
% 3.40/1.58  tff(c_445, plain, (r2_hidden('#skF_11', k3_relat_1('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_435])).
% 3.40/1.58  tff(c_553, plain, (r2_hidden('#skF_11', k1_relat_1('#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_536, c_445])).
% 3.40/1.58  tff(c_255, plain, (![E_127, C_128, A_126, D_125, B_124]: (r2_hidden(k4_tarski(k1_funct_1(C_128, D_125), k1_funct_1(C_128, E_127)), B_124) | ~r2_hidden(k4_tarski(D_125, E_127), A_126) | ~r3_wellord1(A_126, B_124, C_128) | ~v1_funct_1(C_128) | ~v1_relat_1(C_128) | ~v1_relat_1(B_124) | ~v1_relat_1(A_126))), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.40/1.58  tff(c_263, plain, (![C_128, B_124]: (r2_hidden(k4_tarski(k1_funct_1(C_128, '#skF_10'), k1_funct_1(C_128, '#skF_11')), B_124) | ~r3_wellord1('#skF_7', B_124, C_128) | ~v1_funct_1(C_128) | ~v1_relat_1(C_128) | ~v1_relat_1(B_124) | ~v1_relat_1('#skF_7'))), inference(resolution, [status(thm)], [c_66, c_255])).
% 3.40/1.58  tff(c_344, plain, (![C_138, B_139]: (r2_hidden(k4_tarski(k1_funct_1(C_138, '#skF_10'), k1_funct_1(C_138, '#skF_11')), B_139) | ~r3_wellord1('#skF_7', B_139, C_138) | ~v1_funct_1(C_138) | ~v1_relat_1(C_138) | ~v1_relat_1(B_139))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_263])).
% 3.40/1.58  tff(c_62, plain, (k1_funct_1('#skF_9', '#skF_11')=k1_funct_1('#skF_9', '#skF_10') | ~r2_hidden(k4_tarski(k1_funct_1('#skF_9', '#skF_10'), k1_funct_1('#skF_9', '#skF_11')), '#skF_8')), inference(cnfTransformation, [status(thm)], [f_120])).
% 3.40/1.58  tff(c_84, plain, (~r2_hidden(k4_tarski(k1_funct_1('#skF_9', '#skF_10'), k1_funct_1('#skF_9', '#skF_11')), '#skF_8')), inference(splitLeft, [status(thm)], [c_62])).
% 3.40/1.58  tff(c_361, plain, (~r3_wellord1('#skF_7', '#skF_8', '#skF_9') | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9') | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_344, c_84])).
% 3.40/1.58  tff(c_374, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_70, c_68, c_361])).
% 3.40/1.58  tff(c_375, plain, (k1_funct_1('#skF_9', '#skF_11')=k1_funct_1('#skF_9', '#skF_10')), inference(splitRight, [status(thm)], [c_62])).
% 3.40/1.58  tff(c_594, plain, (k9_relat_1('#skF_9', k1_tarski('#skF_11'))=k1_tarski(k1_funct_1('#skF_9', '#skF_11')) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_553, c_588])).
% 3.40/1.58  tff(c_608, plain, (k9_relat_1('#skF_9', k1_tarski('#skF_11'))=k1_tarski(k1_funct_1('#skF_9', '#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_375, c_594])).
% 3.40/1.58  tff(c_832, plain, (k10_relat_1('#skF_9', k1_tarski(k1_funct_1('#skF_9', '#skF_10')))=k1_tarski('#skF_11') | ~v2_funct_1('#skF_9') | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9') | ~r2_hidden('#skF_11', k1_relat_1('#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_608, c_823])).
% 3.40/1.58  tff(c_839, plain, (k10_relat_1('#skF_9', k1_tarski(k1_funct_1('#skF_9', '#skF_10')))=k1_tarski('#skF_11')), inference(demodulation, [status(thm), theory('equality')], [c_553, c_72, c_70, c_489, c_832])).
% 3.40/1.58  tff(c_868, plain, (k1_tarski('#skF_11')=k1_tarski('#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_841, c_839])).
% 3.40/1.58  tff(c_8, plain, (![C_7]: (r2_hidden(C_7, k1_tarski(C_7)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.40/1.58  tff(c_907, plain, (r2_hidden('#skF_11', k1_tarski('#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_868, c_8])).
% 3.40/1.58  tff(c_6, plain, (![C_7, A_3]: (C_7=A_3 | ~r2_hidden(C_7, k1_tarski(A_3)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.40/1.58  tff(c_919, plain, ('#skF_11'='#skF_10'), inference(resolution, [status(thm)], [c_907, c_6])).
% 3.40/1.58  tff(c_923, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_919])).
% 3.40/1.58  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.40/1.58  
% 3.40/1.58  Inference rules
% 3.40/1.58  ----------------------
% 3.40/1.58  #Ref     : 0
% 3.40/1.58  #Sup     : 185
% 3.40/1.58  #Fact    : 0
% 3.40/1.58  #Define  : 0
% 3.40/1.58  #Split   : 2
% 3.40/1.58  #Chain   : 0
% 3.40/1.58  #Close   : 0
% 3.40/1.58  
% 3.40/1.58  Ordering : KBO
% 3.40/1.58  
% 3.40/1.58  Simplification rules
% 3.40/1.58  ----------------------
% 3.40/1.58  #Subsume      : 7
% 3.40/1.58  #Demod        : 119
% 3.40/1.58  #Tautology    : 65
% 3.40/1.58  #SimpNegUnit  : 1
% 3.40/1.58  #BackRed      : 7
% 3.40/1.58  
% 3.40/1.58  #Partial instantiations: 0
% 3.40/1.58  #Strategies tried      : 1
% 3.40/1.58  
% 3.40/1.58  Timing (in seconds)
% 3.40/1.58  ----------------------
% 3.40/1.59  Preprocessing        : 0.37
% 3.40/1.59  Parsing              : 0.19
% 3.40/1.59  CNF conversion       : 0.03
% 3.40/1.59  Main loop            : 0.41
% 3.40/1.59  Inferencing          : 0.15
% 3.40/1.59  Reduction            : 0.12
% 3.40/1.59  Demodulation         : 0.08
% 3.40/1.59  BG Simplification    : 0.03
% 3.40/1.59  Subsumption          : 0.08
% 3.40/1.59  Abstraction          : 0.02
% 3.40/1.59  MUC search           : 0.00
% 3.40/1.59  Cooper               : 0.00
% 3.40/1.59  Total                : 0.81
% 3.40/1.59  Index Insertion      : 0.00
% 3.40/1.59  Index Deletion       : 0.00
% 3.40/1.59  Index Matching       : 0.00
% 3.40/1.59  BG Taut test         : 0.00
%------------------------------------------------------------------------------
