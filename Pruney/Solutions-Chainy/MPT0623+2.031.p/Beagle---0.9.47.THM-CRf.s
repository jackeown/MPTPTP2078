%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:10 EST 2020

% Result     : Theorem 5.42s
% Output     : CNFRefutation 5.55s
% Verified   : 
% Statistics : Number of formulae       :  119 ( 528 expanded)
%              Number of leaves         :   36 ( 186 expanded)
%              Depth                    :   15
%              Number of atoms          :  197 (1420 expanded)
%              Number of equality atoms :  109 ( 819 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_11 > #skF_8 > #skF_3 > #skF_10 > #skF_7 > #skF_2 > #skF_1 > #skF_9 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': $i )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_8',type,(
    '#skF_8': $i > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i ) > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_84,axiom,(
    ! [A] :
    ? [B] :
      ( v1_relat_1(B)
      & v1_funct_1(B)
      & k1_relat_1(B) = A
      & ! [C] :
          ( r2_hidden(C,A)
         => k1_funct_1(B,C) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s3_funct_1__e2_25__funct_1)).

tff(f_115,negated_conjecture,(
    ~ ! [A,B] :
        ~ ( ~ ( A = k1_xboole_0
              & B != k1_xboole_0 )
          & ! [C] :
              ( ( v1_relat_1(C)
                & v1_funct_1(C) )
             => ~ ( B = k1_relat_1(C)
                  & r1_tarski(k2_relat_1(C),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_funct_1)).

tff(f_66,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_50,axiom,(
    ! [A,B] : ~ r2_hidden(A,k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).

tff(f_97,axiom,(
    ! [A] :
      ( A != k1_xboole_0
     => ! [B] :
        ? [C] :
          ( v1_relat_1(C)
          & v1_funct_1(C)
          & k1_relat_1(C) = A
          & k2_relat_1(C) = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_funct_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_41,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_34,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_72,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k1_relat_1(A) = k1_xboole_0
      <=> k2_relat_1(A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).

tff(c_52,plain,(
    ! [A_37] : k1_relat_1('#skF_8'(A_37)) = A_37 ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_56,plain,(
    ! [A_37] : v1_relat_1('#skF_8'(A_37)) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_68,plain,
    ( k1_xboole_0 = '#skF_11'
    | k1_xboole_0 != '#skF_10' ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_104,plain,(
    k1_xboole_0 != '#skF_10' ),
    inference(splitLeft,[status(thm)],[c_68])).

tff(c_131,plain,(
    ! [A_69] :
      ( k1_relat_1(A_69) != k1_xboole_0
      | k1_xboole_0 = A_69
      | ~ v1_relat_1(A_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_137,plain,(
    ! [A_37] :
      ( k1_relat_1('#skF_8'(A_37)) != k1_xboole_0
      | '#skF_8'(A_37) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_56,c_131])).

tff(c_142,plain,(
    ! [A_70] :
      ( k1_xboole_0 != A_70
      | '#skF_8'(A_70) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_137])).

tff(c_214,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_142,c_52])).

tff(c_1541,plain,(
    ! [A_214,B_215] :
      ( r2_hidden(k4_tarski('#skF_4'(A_214,B_215),'#skF_5'(A_214,B_215)),A_214)
      | r2_hidden('#skF_6'(A_214,B_215),B_215)
      | k1_relat_1(A_214) = B_215 ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_24,plain,(
    ! [A_12] : k2_zfmisc_1(A_12,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_106,plain,(
    ! [A_59,B_60] : ~ r2_hidden(A_59,k2_zfmisc_1(A_59,B_60)) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_109,plain,(
    ! [A_12] : ~ r2_hidden(A_12,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_106])).

tff(c_1572,plain,(
    ! [B_215] :
      ( r2_hidden('#skF_6'(k1_xboole_0,B_215),B_215)
      | k1_relat_1(k1_xboole_0) = B_215 ) ),
    inference(resolution,[status(thm)],[c_1541,c_109])).

tff(c_1582,plain,(
    ! [B_215] :
      ( r2_hidden('#skF_6'(k1_xboole_0,B_215),B_215)
      | k1_xboole_0 = B_215 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_214,c_1572])).

tff(c_60,plain,(
    ! [A_43,B_47] :
      ( k1_relat_1('#skF_9'(A_43,B_47)) = A_43
      | k1_xboole_0 = A_43 ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_62,plain,(
    ! [A_43,B_47] :
      ( v1_funct_1('#skF_9'(A_43,B_47))
      | k1_xboole_0 = A_43 ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_64,plain,(
    ! [A_43,B_47] :
      ( v1_relat_1('#skF_9'(A_43,B_47))
      | k1_xboole_0 = A_43 ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_316,plain,(
    ! [A_88,B_89] :
      ( r2_hidden('#skF_1'(A_88,B_89),A_88)
      | r1_tarski(A_88,B_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_10,plain,(
    ! [C_11,A_7] :
      ( C_11 = A_7
      | ~ r2_hidden(C_11,k1_tarski(A_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_374,plain,(
    ! [A_103,B_104] :
      ( '#skF_1'(k1_tarski(A_103),B_104) = A_103
      | r1_tarski(k1_tarski(A_103),B_104) ) ),
    inference(resolution,[status(thm)],[c_316,c_10])).

tff(c_302,plain,(
    ! [A_82,B_83] :
      ( k2_relat_1('#skF_9'(A_82,B_83)) = k1_tarski(B_83)
      | k1_xboole_0 = A_82 ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_66,plain,(
    ! [C_50] :
      ( ~ r1_tarski(k2_relat_1(C_50),'#skF_10')
      | k1_relat_1(C_50) != '#skF_11'
      | ~ v1_funct_1(C_50)
      | ~ v1_relat_1(C_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_308,plain,(
    ! [B_83,A_82] :
      ( ~ r1_tarski(k1_tarski(B_83),'#skF_10')
      | k1_relat_1('#skF_9'(A_82,B_83)) != '#skF_11'
      | ~ v1_funct_1('#skF_9'(A_82,B_83))
      | ~ v1_relat_1('#skF_9'(A_82,B_83))
      | k1_xboole_0 = A_82 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_302,c_66])).

tff(c_399,plain,(
    ! [A_107,A_108] :
      ( k1_relat_1('#skF_9'(A_107,A_108)) != '#skF_11'
      | ~ v1_funct_1('#skF_9'(A_107,A_108))
      | ~ v1_relat_1('#skF_9'(A_107,A_108))
      | k1_xboole_0 = A_107
      | '#skF_1'(k1_tarski(A_108),'#skF_10') = A_108 ) ),
    inference(resolution,[status(thm)],[c_374,c_308])).

tff(c_728,plain,(
    ! [A_143,B_144] :
      ( k1_relat_1('#skF_9'(A_143,B_144)) != '#skF_11'
      | ~ v1_funct_1('#skF_9'(A_143,B_144))
      | '#skF_1'(k1_tarski(B_144),'#skF_10') = B_144
      | k1_xboole_0 = A_143 ) ),
    inference(resolution,[status(thm)],[c_64,c_399])).

tff(c_948,plain,(
    ! [A_173,B_174] :
      ( k1_relat_1('#skF_9'(A_173,B_174)) != '#skF_11'
      | '#skF_1'(k1_tarski(B_174),'#skF_10') = B_174
      | k1_xboole_0 = A_173 ) ),
    inference(resolution,[status(thm)],[c_62,c_728])).

tff(c_951,plain,(
    ! [A_43,B_47] :
      ( A_43 != '#skF_11'
      | '#skF_1'(k1_tarski(B_47),'#skF_10') = B_47
      | k1_xboole_0 = A_43
      | k1_xboole_0 = A_43 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_948])).

tff(c_953,plain,(
    k1_xboole_0 = '#skF_11' ),
    inference(splitLeft,[status(thm)],[c_951])).

tff(c_152,plain,(
    ! [A_70] :
      ( v1_relat_1(k1_xboole_0)
      | k1_xboole_0 != A_70 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_142,c_56])).

tff(c_179,plain,(
    ! [A_70] : k1_xboole_0 != A_70 ),
    inference(splitLeft,[status(thm)],[c_152])).

tff(c_188,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_179,c_24])).

tff(c_189,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_152])).

tff(c_54,plain,(
    ! [A_37] : v1_funct_1('#skF_8'(A_37)) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_150,plain,(
    ! [A_70] :
      ( v1_funct_1(k1_xboole_0)
      | k1_xboole_0 != A_70 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_142,c_54])).

tff(c_168,plain,(
    ! [A_70] : k1_xboole_0 != A_70 ),
    inference(splitLeft,[status(thm)],[c_150])).

tff(c_177,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_168,c_24])).

tff(c_178,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_150])).

tff(c_8,plain,(
    ! [A_6] : r1_tarski(k1_xboole_0,A_6) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_224,plain,(
    ! [A_76] :
      ( k2_relat_1(A_76) = k1_xboole_0
      | k1_relat_1(A_76) != k1_xboole_0
      | ~ v1_relat_1(A_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_227,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0
    | k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_189,c_224])).

tff(c_236,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_214,c_227])).

tff(c_243,plain,
    ( ~ r1_tarski(k1_xboole_0,'#skF_10')
    | k1_relat_1(k1_xboole_0) != '#skF_11'
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_236,c_66])).

tff(c_247,plain,(
    k1_xboole_0 != '#skF_11' ),
    inference(demodulation,[status(thm),theory(equality)],[c_189,c_178,c_214,c_8,c_243])).

tff(c_996,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_953,c_247])).

tff(c_999,plain,(
    ! [B_175] : '#skF_1'(k1_tarski(B_175),'#skF_10') = B_175 ),
    inference(splitRight,[status(thm)],[c_951])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1033,plain,(
    ! [B_176] :
      ( ~ r2_hidden(B_176,'#skF_10')
      | r1_tarski(k1_tarski(B_176),'#skF_10') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_999,c_4])).

tff(c_1948,plain,(
    ! [A_232,B_233] :
      ( k1_relat_1('#skF_9'(A_232,B_233)) != '#skF_11'
      | ~ v1_funct_1('#skF_9'(A_232,B_233))
      | ~ v1_relat_1('#skF_9'(A_232,B_233))
      | k1_xboole_0 = A_232
      | ~ r2_hidden(B_233,'#skF_10') ) ),
    inference(resolution,[status(thm)],[c_1033,c_308])).

tff(c_2703,plain,(
    ! [A_260,B_261] :
      ( k1_relat_1('#skF_9'(A_260,B_261)) != '#skF_11'
      | ~ v1_funct_1('#skF_9'(A_260,B_261))
      | ~ r2_hidden(B_261,'#skF_10')
      | k1_xboole_0 = A_260 ) ),
    inference(resolution,[status(thm)],[c_64,c_1948])).

tff(c_3008,plain,(
    ! [A_277,B_278] :
      ( k1_relat_1('#skF_9'(A_277,B_278)) != '#skF_11'
      | ~ r2_hidden(B_278,'#skF_10')
      | k1_xboole_0 = A_277 ) ),
    inference(resolution,[status(thm)],[c_62,c_2703])).

tff(c_3017,plain,(
    ! [A_43,B_47] :
      ( A_43 != '#skF_11'
      | ~ r2_hidden(B_47,'#skF_10')
      | k1_xboole_0 = A_43
      | k1_xboole_0 = A_43 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_3008])).

tff(c_6253,plain,(
    ! [B_4180] : ~ r2_hidden(B_4180,'#skF_10') ),
    inference(splitLeft,[status(thm)],[c_3017])).

tff(c_6263,plain,(
    k1_xboole_0 = '#skF_10' ),
    inference(resolution,[status(thm)],[c_1582,c_6253])).

tff(c_6296,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_104,c_6263])).

tff(c_6298,plain,(
    k1_xboole_0 = '#skF_11' ),
    inference(splitRight,[status(thm)],[c_3017])).

tff(c_6398,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6298,c_247])).

tff(c_6400,plain,(
    k1_xboole_0 = '#skF_10' ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_44,plain,(
    ! [A_35] :
      ( k1_relat_1(A_35) != k1_xboole_0
      | k1_xboole_0 = A_35
      | ~ v1_relat_1(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_6486,plain,(
    ! [A_4225] :
      ( k1_relat_1(A_4225) != '#skF_10'
      | A_4225 = '#skF_10'
      | ~ v1_relat_1(A_4225) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6400,c_6400,c_44])).

tff(c_6492,plain,(
    ! [A_37] :
      ( k1_relat_1('#skF_8'(A_37)) != '#skF_10'
      | '#skF_8'(A_37) = '#skF_10' ) ),
    inference(resolution,[status(thm)],[c_56,c_6486])).

tff(c_6498,plain,(
    ! [A_4228] :
      ( A_4228 != '#skF_10'
      | '#skF_8'(A_4228) = '#skF_10' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_6492])).

tff(c_6508,plain,(
    ! [A_4228] :
      ( v1_relat_1('#skF_10')
      | A_4228 != '#skF_10' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6498,c_56])).

tff(c_6545,plain,(
    ! [A_4228] : A_4228 != '#skF_10' ),
    inference(splitLeft,[status(thm)],[c_6508])).

tff(c_6399,plain,(
    k1_xboole_0 = '#skF_11' ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_6409,plain,(
    '#skF_11' = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6400,c_6399])).

tff(c_6401,plain,(
    ! [A_12] : k2_zfmisc_1(A_12,'#skF_11') = '#skF_11' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6399,c_6399,c_24])).

tff(c_6429,plain,(
    ! [A_12] : k2_zfmisc_1(A_12,'#skF_10') = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6409,c_6409,c_6401])).

tff(c_6556,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6545,c_6429])).

tff(c_6557,plain,(
    v1_relat_1('#skF_10') ),
    inference(splitRight,[status(thm)],[c_6508])).

tff(c_6506,plain,(
    ! [A_4228] :
      ( v1_funct_1('#skF_10')
      | A_4228 != '#skF_10' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6498,c_54])).

tff(c_6514,plain,(
    ! [A_4228] : A_4228 != '#skF_10' ),
    inference(splitLeft,[status(thm)],[c_6506])).

tff(c_6525,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6514,c_6429])).

tff(c_6526,plain,(
    v1_funct_1('#skF_10') ),
    inference(splitRight,[status(thm)],[c_6506])).

tff(c_6580,plain,(
    k1_relat_1('#skF_10') = '#skF_10' ),
    inference(superposition,[status(thm),theory(equality)],[c_6498,c_52])).

tff(c_6527,plain,(
    ! [A_4229,B_4230] :
      ( r2_hidden('#skF_1'(A_4229,B_4230),A_4229)
      | r1_tarski(A_4229,B_4230) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_6540,plain,(
    ! [A_4229] : r1_tarski(A_4229,A_4229) ),
    inference(resolution,[status(thm)],[c_6527,c_4])).

tff(c_48,plain,(
    ! [A_36] :
      ( k2_relat_1(A_36) = k1_xboole_0
      | k1_relat_1(A_36) != k1_xboole_0
      | ~ v1_relat_1(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_6624,plain,(
    ! [A_4240] :
      ( k2_relat_1(A_4240) = '#skF_10'
      | k1_relat_1(A_4240) != '#skF_10'
      | ~ v1_relat_1(A_4240) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6400,c_6400,c_48])).

tff(c_6627,plain,
    ( k2_relat_1('#skF_10') = '#skF_10'
    | k1_relat_1('#skF_10') != '#skF_10' ),
    inference(resolution,[status(thm)],[c_6557,c_6624])).

tff(c_6636,plain,(
    k2_relat_1('#skF_10') = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6580,c_6627])).

tff(c_6414,plain,(
    ! [C_50] :
      ( ~ r1_tarski(k2_relat_1(C_50),'#skF_10')
      | k1_relat_1(C_50) != '#skF_10'
      | ~ v1_funct_1(C_50)
      | ~ v1_relat_1(C_50) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6409,c_66])).

tff(c_6643,plain,
    ( ~ r1_tarski('#skF_10','#skF_10')
    | k1_relat_1('#skF_10') != '#skF_10'
    | ~ v1_funct_1('#skF_10')
    | ~ v1_relat_1('#skF_10') ),
    inference(superposition,[status(thm),theory(equality)],[c_6636,c_6414])).

tff(c_6648,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6557,c_6526,c_6580,c_6540,c_6643])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 09:33:35 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.42/2.05  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.42/2.06  
% 5.42/2.06  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.42/2.06  %$ r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_11 > #skF_8 > #skF_3 > #skF_10 > #skF_7 > #skF_2 > #skF_1 > #skF_9 > #skF_5 > #skF_4
% 5.42/2.06  
% 5.42/2.06  %Foreground sorts:
% 5.42/2.06  
% 5.42/2.06  
% 5.42/2.06  %Background operators:
% 5.42/2.06  
% 5.42/2.06  
% 5.42/2.06  %Foreground operators:
% 5.42/2.06  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 5.42/2.06  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.42/2.06  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.42/2.06  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.42/2.06  tff('#skF_11', type, '#skF_11': $i).
% 5.42/2.06  tff(k1_tarski, type, k1_tarski: $i > $i).
% 5.42/2.06  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 5.42/2.06  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.42/2.06  tff('#skF_8', type, '#skF_8': $i > $i).
% 5.42/2.06  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 5.42/2.06  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.42/2.06  tff('#skF_10', type, '#skF_10': $i).
% 5.42/2.06  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.42/2.06  tff('#skF_7', type, '#skF_7': ($i * $i * $i) > $i).
% 5.42/2.06  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 5.42/2.06  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.42/2.06  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.42/2.06  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.42/2.06  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.42/2.06  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 5.42/2.06  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.42/2.06  tff('#skF_9', type, '#skF_9': ($i * $i) > $i).
% 5.42/2.06  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 5.42/2.06  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.42/2.06  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 5.42/2.06  
% 5.55/2.08  tff(f_84, axiom, (![A]: (?[B]: (((v1_relat_1(B) & v1_funct_1(B)) & (k1_relat_1(B) = A)) & (![C]: (r2_hidden(C, A) => (k1_funct_1(B, C) = k1_xboole_0)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', s3_funct_1__e2_25__funct_1)).
% 5.55/2.08  tff(f_115, negated_conjecture, ~(![A, B]: ~(~((A = k1_xboole_0) & ~(B = k1_xboole_0)) & (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => ~((B = k1_relat_1(C)) & r1_tarski(k2_relat_1(C), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_funct_1)).
% 5.55/2.08  tff(f_66, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_relat_1)).
% 5.55/2.08  tff(f_58, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_relat_1)).
% 5.55/2.08  tff(f_47, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 5.55/2.08  tff(f_50, axiom, (![A, B]: ~r2_hidden(A, k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 5.55/2.08  tff(f_97, axiom, (![A]: (~(A = k1_xboole_0) => (![B]: (?[C]: (((v1_relat_1(C) & v1_funct_1(C)) & (k1_relat_1(C) = A)) & (k2_relat_1(C) = k1_tarski(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t15_funct_1)).
% 5.55/2.08  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 5.55/2.08  tff(f_41, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 5.55/2.08  tff(f_34, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 5.55/2.08  tff(f_72, axiom, (![A]: (v1_relat_1(A) => ((k1_relat_1(A) = k1_xboole_0) <=> (k2_relat_1(A) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_relat_1)).
% 5.55/2.08  tff(c_52, plain, (![A_37]: (k1_relat_1('#skF_8'(A_37))=A_37)), inference(cnfTransformation, [status(thm)], [f_84])).
% 5.55/2.08  tff(c_56, plain, (![A_37]: (v1_relat_1('#skF_8'(A_37)))), inference(cnfTransformation, [status(thm)], [f_84])).
% 5.55/2.08  tff(c_68, plain, (k1_xboole_0='#skF_11' | k1_xboole_0!='#skF_10'), inference(cnfTransformation, [status(thm)], [f_115])).
% 5.55/2.08  tff(c_104, plain, (k1_xboole_0!='#skF_10'), inference(splitLeft, [status(thm)], [c_68])).
% 5.55/2.08  tff(c_131, plain, (![A_69]: (k1_relat_1(A_69)!=k1_xboole_0 | k1_xboole_0=A_69 | ~v1_relat_1(A_69))), inference(cnfTransformation, [status(thm)], [f_66])).
% 5.55/2.08  tff(c_137, plain, (![A_37]: (k1_relat_1('#skF_8'(A_37))!=k1_xboole_0 | '#skF_8'(A_37)=k1_xboole_0)), inference(resolution, [status(thm)], [c_56, c_131])).
% 5.55/2.08  tff(c_142, plain, (![A_70]: (k1_xboole_0!=A_70 | '#skF_8'(A_70)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_52, c_137])).
% 5.55/2.08  tff(c_214, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_142, c_52])).
% 5.55/2.08  tff(c_1541, plain, (![A_214, B_215]: (r2_hidden(k4_tarski('#skF_4'(A_214, B_215), '#skF_5'(A_214, B_215)), A_214) | r2_hidden('#skF_6'(A_214, B_215), B_215) | k1_relat_1(A_214)=B_215)), inference(cnfTransformation, [status(thm)], [f_58])).
% 5.55/2.08  tff(c_24, plain, (![A_12]: (k2_zfmisc_1(A_12, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.55/2.08  tff(c_106, plain, (![A_59, B_60]: (~r2_hidden(A_59, k2_zfmisc_1(A_59, B_60)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 5.55/2.08  tff(c_109, plain, (![A_12]: (~r2_hidden(A_12, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_24, c_106])).
% 5.55/2.08  tff(c_1572, plain, (![B_215]: (r2_hidden('#skF_6'(k1_xboole_0, B_215), B_215) | k1_relat_1(k1_xboole_0)=B_215)), inference(resolution, [status(thm)], [c_1541, c_109])).
% 5.55/2.08  tff(c_1582, plain, (![B_215]: (r2_hidden('#skF_6'(k1_xboole_0, B_215), B_215) | k1_xboole_0=B_215)), inference(demodulation, [status(thm), theory('equality')], [c_214, c_1572])).
% 5.55/2.08  tff(c_60, plain, (![A_43, B_47]: (k1_relat_1('#skF_9'(A_43, B_47))=A_43 | k1_xboole_0=A_43)), inference(cnfTransformation, [status(thm)], [f_97])).
% 5.55/2.08  tff(c_62, plain, (![A_43, B_47]: (v1_funct_1('#skF_9'(A_43, B_47)) | k1_xboole_0=A_43)), inference(cnfTransformation, [status(thm)], [f_97])).
% 5.55/2.08  tff(c_64, plain, (![A_43, B_47]: (v1_relat_1('#skF_9'(A_43, B_47)) | k1_xboole_0=A_43)), inference(cnfTransformation, [status(thm)], [f_97])).
% 5.55/2.08  tff(c_316, plain, (![A_88, B_89]: (r2_hidden('#skF_1'(A_88, B_89), A_88) | r1_tarski(A_88, B_89))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.55/2.08  tff(c_10, plain, (![C_11, A_7]: (C_11=A_7 | ~r2_hidden(C_11, k1_tarski(A_7)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.55/2.08  tff(c_374, plain, (![A_103, B_104]: ('#skF_1'(k1_tarski(A_103), B_104)=A_103 | r1_tarski(k1_tarski(A_103), B_104))), inference(resolution, [status(thm)], [c_316, c_10])).
% 5.55/2.08  tff(c_302, plain, (![A_82, B_83]: (k2_relat_1('#skF_9'(A_82, B_83))=k1_tarski(B_83) | k1_xboole_0=A_82)), inference(cnfTransformation, [status(thm)], [f_97])).
% 5.55/2.08  tff(c_66, plain, (![C_50]: (~r1_tarski(k2_relat_1(C_50), '#skF_10') | k1_relat_1(C_50)!='#skF_11' | ~v1_funct_1(C_50) | ~v1_relat_1(C_50))), inference(cnfTransformation, [status(thm)], [f_115])).
% 5.55/2.08  tff(c_308, plain, (![B_83, A_82]: (~r1_tarski(k1_tarski(B_83), '#skF_10') | k1_relat_1('#skF_9'(A_82, B_83))!='#skF_11' | ~v1_funct_1('#skF_9'(A_82, B_83)) | ~v1_relat_1('#skF_9'(A_82, B_83)) | k1_xboole_0=A_82)), inference(superposition, [status(thm), theory('equality')], [c_302, c_66])).
% 5.55/2.08  tff(c_399, plain, (![A_107, A_108]: (k1_relat_1('#skF_9'(A_107, A_108))!='#skF_11' | ~v1_funct_1('#skF_9'(A_107, A_108)) | ~v1_relat_1('#skF_9'(A_107, A_108)) | k1_xboole_0=A_107 | '#skF_1'(k1_tarski(A_108), '#skF_10')=A_108)), inference(resolution, [status(thm)], [c_374, c_308])).
% 5.55/2.08  tff(c_728, plain, (![A_143, B_144]: (k1_relat_1('#skF_9'(A_143, B_144))!='#skF_11' | ~v1_funct_1('#skF_9'(A_143, B_144)) | '#skF_1'(k1_tarski(B_144), '#skF_10')=B_144 | k1_xboole_0=A_143)), inference(resolution, [status(thm)], [c_64, c_399])).
% 5.55/2.08  tff(c_948, plain, (![A_173, B_174]: (k1_relat_1('#skF_9'(A_173, B_174))!='#skF_11' | '#skF_1'(k1_tarski(B_174), '#skF_10')=B_174 | k1_xboole_0=A_173)), inference(resolution, [status(thm)], [c_62, c_728])).
% 5.55/2.08  tff(c_951, plain, (![A_43, B_47]: (A_43!='#skF_11' | '#skF_1'(k1_tarski(B_47), '#skF_10')=B_47 | k1_xboole_0=A_43 | k1_xboole_0=A_43)), inference(superposition, [status(thm), theory('equality')], [c_60, c_948])).
% 5.55/2.08  tff(c_953, plain, (k1_xboole_0='#skF_11'), inference(splitLeft, [status(thm)], [c_951])).
% 5.55/2.08  tff(c_152, plain, (![A_70]: (v1_relat_1(k1_xboole_0) | k1_xboole_0!=A_70)), inference(superposition, [status(thm), theory('equality')], [c_142, c_56])).
% 5.55/2.08  tff(c_179, plain, (![A_70]: (k1_xboole_0!=A_70)), inference(splitLeft, [status(thm)], [c_152])).
% 5.55/2.08  tff(c_188, plain, $false, inference(negUnitSimplification, [status(thm)], [c_179, c_24])).
% 5.55/2.08  tff(c_189, plain, (v1_relat_1(k1_xboole_0)), inference(splitRight, [status(thm)], [c_152])).
% 5.55/2.08  tff(c_54, plain, (![A_37]: (v1_funct_1('#skF_8'(A_37)))), inference(cnfTransformation, [status(thm)], [f_84])).
% 5.55/2.08  tff(c_150, plain, (![A_70]: (v1_funct_1(k1_xboole_0) | k1_xboole_0!=A_70)), inference(superposition, [status(thm), theory('equality')], [c_142, c_54])).
% 5.55/2.08  tff(c_168, plain, (![A_70]: (k1_xboole_0!=A_70)), inference(splitLeft, [status(thm)], [c_150])).
% 5.55/2.08  tff(c_177, plain, $false, inference(negUnitSimplification, [status(thm)], [c_168, c_24])).
% 5.55/2.08  tff(c_178, plain, (v1_funct_1(k1_xboole_0)), inference(splitRight, [status(thm)], [c_150])).
% 5.55/2.08  tff(c_8, plain, (![A_6]: (r1_tarski(k1_xboole_0, A_6))), inference(cnfTransformation, [status(thm)], [f_34])).
% 5.55/2.08  tff(c_224, plain, (![A_76]: (k2_relat_1(A_76)=k1_xboole_0 | k1_relat_1(A_76)!=k1_xboole_0 | ~v1_relat_1(A_76))), inference(cnfTransformation, [status(thm)], [f_72])).
% 5.55/2.08  tff(c_227, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0 | k1_relat_1(k1_xboole_0)!=k1_xboole_0), inference(resolution, [status(thm)], [c_189, c_224])).
% 5.55/2.08  tff(c_236, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_214, c_227])).
% 5.55/2.08  tff(c_243, plain, (~r1_tarski(k1_xboole_0, '#skF_10') | k1_relat_1(k1_xboole_0)!='#skF_11' | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_236, c_66])).
% 5.55/2.08  tff(c_247, plain, (k1_xboole_0!='#skF_11'), inference(demodulation, [status(thm), theory('equality')], [c_189, c_178, c_214, c_8, c_243])).
% 5.55/2.08  tff(c_996, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_953, c_247])).
% 5.55/2.08  tff(c_999, plain, (![B_175]: ('#skF_1'(k1_tarski(B_175), '#skF_10')=B_175)), inference(splitRight, [status(thm)], [c_951])).
% 5.55/2.08  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.55/2.08  tff(c_1033, plain, (![B_176]: (~r2_hidden(B_176, '#skF_10') | r1_tarski(k1_tarski(B_176), '#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_999, c_4])).
% 5.55/2.08  tff(c_1948, plain, (![A_232, B_233]: (k1_relat_1('#skF_9'(A_232, B_233))!='#skF_11' | ~v1_funct_1('#skF_9'(A_232, B_233)) | ~v1_relat_1('#skF_9'(A_232, B_233)) | k1_xboole_0=A_232 | ~r2_hidden(B_233, '#skF_10'))), inference(resolution, [status(thm)], [c_1033, c_308])).
% 5.55/2.08  tff(c_2703, plain, (![A_260, B_261]: (k1_relat_1('#skF_9'(A_260, B_261))!='#skF_11' | ~v1_funct_1('#skF_9'(A_260, B_261)) | ~r2_hidden(B_261, '#skF_10') | k1_xboole_0=A_260)), inference(resolution, [status(thm)], [c_64, c_1948])).
% 5.55/2.08  tff(c_3008, plain, (![A_277, B_278]: (k1_relat_1('#skF_9'(A_277, B_278))!='#skF_11' | ~r2_hidden(B_278, '#skF_10') | k1_xboole_0=A_277)), inference(resolution, [status(thm)], [c_62, c_2703])).
% 5.55/2.08  tff(c_3017, plain, (![A_43, B_47]: (A_43!='#skF_11' | ~r2_hidden(B_47, '#skF_10') | k1_xboole_0=A_43 | k1_xboole_0=A_43)), inference(superposition, [status(thm), theory('equality')], [c_60, c_3008])).
% 5.55/2.08  tff(c_6253, plain, (![B_4180]: (~r2_hidden(B_4180, '#skF_10'))), inference(splitLeft, [status(thm)], [c_3017])).
% 5.55/2.08  tff(c_6263, plain, (k1_xboole_0='#skF_10'), inference(resolution, [status(thm)], [c_1582, c_6253])).
% 5.55/2.08  tff(c_6296, plain, $false, inference(negUnitSimplification, [status(thm)], [c_104, c_6263])).
% 5.55/2.08  tff(c_6298, plain, (k1_xboole_0='#skF_11'), inference(splitRight, [status(thm)], [c_3017])).
% 5.55/2.08  tff(c_6398, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6298, c_247])).
% 5.55/2.08  tff(c_6400, plain, (k1_xboole_0='#skF_10'), inference(splitRight, [status(thm)], [c_68])).
% 5.55/2.08  tff(c_44, plain, (![A_35]: (k1_relat_1(A_35)!=k1_xboole_0 | k1_xboole_0=A_35 | ~v1_relat_1(A_35))), inference(cnfTransformation, [status(thm)], [f_66])).
% 5.55/2.08  tff(c_6486, plain, (![A_4225]: (k1_relat_1(A_4225)!='#skF_10' | A_4225='#skF_10' | ~v1_relat_1(A_4225))), inference(demodulation, [status(thm), theory('equality')], [c_6400, c_6400, c_44])).
% 5.55/2.08  tff(c_6492, plain, (![A_37]: (k1_relat_1('#skF_8'(A_37))!='#skF_10' | '#skF_8'(A_37)='#skF_10')), inference(resolution, [status(thm)], [c_56, c_6486])).
% 5.55/2.08  tff(c_6498, plain, (![A_4228]: (A_4228!='#skF_10' | '#skF_8'(A_4228)='#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_6492])).
% 5.55/2.08  tff(c_6508, plain, (![A_4228]: (v1_relat_1('#skF_10') | A_4228!='#skF_10')), inference(superposition, [status(thm), theory('equality')], [c_6498, c_56])).
% 5.55/2.08  tff(c_6545, plain, (![A_4228]: (A_4228!='#skF_10')), inference(splitLeft, [status(thm)], [c_6508])).
% 5.55/2.08  tff(c_6399, plain, (k1_xboole_0='#skF_11'), inference(splitRight, [status(thm)], [c_68])).
% 5.55/2.08  tff(c_6409, plain, ('#skF_11'='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_6400, c_6399])).
% 5.55/2.08  tff(c_6401, plain, (![A_12]: (k2_zfmisc_1(A_12, '#skF_11')='#skF_11')), inference(demodulation, [status(thm), theory('equality')], [c_6399, c_6399, c_24])).
% 5.55/2.08  tff(c_6429, plain, (![A_12]: (k2_zfmisc_1(A_12, '#skF_10')='#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_6409, c_6409, c_6401])).
% 5.55/2.08  tff(c_6556, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6545, c_6429])).
% 5.55/2.08  tff(c_6557, plain, (v1_relat_1('#skF_10')), inference(splitRight, [status(thm)], [c_6508])).
% 5.55/2.08  tff(c_6506, plain, (![A_4228]: (v1_funct_1('#skF_10') | A_4228!='#skF_10')), inference(superposition, [status(thm), theory('equality')], [c_6498, c_54])).
% 5.55/2.08  tff(c_6514, plain, (![A_4228]: (A_4228!='#skF_10')), inference(splitLeft, [status(thm)], [c_6506])).
% 5.55/2.08  tff(c_6525, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6514, c_6429])).
% 5.55/2.08  tff(c_6526, plain, (v1_funct_1('#skF_10')), inference(splitRight, [status(thm)], [c_6506])).
% 5.55/2.08  tff(c_6580, plain, (k1_relat_1('#skF_10')='#skF_10'), inference(superposition, [status(thm), theory('equality')], [c_6498, c_52])).
% 5.55/2.08  tff(c_6527, plain, (![A_4229, B_4230]: (r2_hidden('#skF_1'(A_4229, B_4230), A_4229) | r1_tarski(A_4229, B_4230))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.55/2.08  tff(c_6540, plain, (![A_4229]: (r1_tarski(A_4229, A_4229))), inference(resolution, [status(thm)], [c_6527, c_4])).
% 5.55/2.08  tff(c_48, plain, (![A_36]: (k2_relat_1(A_36)=k1_xboole_0 | k1_relat_1(A_36)!=k1_xboole_0 | ~v1_relat_1(A_36))), inference(cnfTransformation, [status(thm)], [f_72])).
% 5.55/2.08  tff(c_6624, plain, (![A_4240]: (k2_relat_1(A_4240)='#skF_10' | k1_relat_1(A_4240)!='#skF_10' | ~v1_relat_1(A_4240))), inference(demodulation, [status(thm), theory('equality')], [c_6400, c_6400, c_48])).
% 5.55/2.08  tff(c_6627, plain, (k2_relat_1('#skF_10')='#skF_10' | k1_relat_1('#skF_10')!='#skF_10'), inference(resolution, [status(thm)], [c_6557, c_6624])).
% 5.55/2.08  tff(c_6636, plain, (k2_relat_1('#skF_10')='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_6580, c_6627])).
% 5.55/2.08  tff(c_6414, plain, (![C_50]: (~r1_tarski(k2_relat_1(C_50), '#skF_10') | k1_relat_1(C_50)!='#skF_10' | ~v1_funct_1(C_50) | ~v1_relat_1(C_50))), inference(demodulation, [status(thm), theory('equality')], [c_6409, c_66])).
% 5.55/2.08  tff(c_6643, plain, (~r1_tarski('#skF_10', '#skF_10') | k1_relat_1('#skF_10')!='#skF_10' | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10')), inference(superposition, [status(thm), theory('equality')], [c_6636, c_6414])).
% 5.55/2.08  tff(c_6648, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6557, c_6526, c_6580, c_6540, c_6643])).
% 5.55/2.08  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.55/2.08  
% 5.55/2.08  Inference rules
% 5.55/2.08  ----------------------
% 5.55/2.08  #Ref     : 3
% 5.55/2.08  #Sup     : 1267
% 5.55/2.08  #Fact    : 0
% 5.55/2.08  #Define  : 0
% 5.55/2.08  #Split   : 8
% 5.55/2.08  #Chain   : 0
% 5.55/2.08  #Close   : 0
% 5.55/2.08  
% 5.55/2.08  Ordering : KBO
% 5.55/2.08  
% 5.55/2.08  Simplification rules
% 5.55/2.08  ----------------------
% 5.55/2.08  #Subsume      : 509
% 5.55/2.08  #Demod        : 772
% 5.55/2.08  #Tautology    : 499
% 5.55/2.08  #SimpNegUnit  : 77
% 5.55/2.08  #BackRed      : 168
% 5.55/2.08  
% 5.55/2.08  #Partial instantiations: 2556
% 5.55/2.08  #Strategies tried      : 1
% 5.55/2.08  
% 5.55/2.08  Timing (in seconds)
% 5.55/2.08  ----------------------
% 5.55/2.08  Preprocessing        : 0.31
% 5.55/2.08  Parsing              : 0.16
% 5.55/2.08  CNF conversion       : 0.03
% 5.55/2.08  Main loop            : 0.97
% 5.55/2.08  Inferencing          : 0.37
% 5.55/2.08  Reduction            : 0.29
% 5.55/2.08  Demodulation         : 0.19
% 5.55/2.08  BG Simplification    : 0.04
% 5.55/2.08  Subsumption          : 0.20
% 5.55/2.08  Abstraction          : 0.05
% 5.55/2.08  MUC search           : 0.00
% 5.55/2.08  Cooper               : 0.00
% 5.55/2.08  Total                : 1.32
% 5.55/2.08  Index Insertion      : 0.00
% 5.55/2.08  Index Deletion       : 0.00
% 5.55/2.09  Index Matching       : 0.00
% 5.55/2.09  BG Taut test         : 0.00
%------------------------------------------------------------------------------
