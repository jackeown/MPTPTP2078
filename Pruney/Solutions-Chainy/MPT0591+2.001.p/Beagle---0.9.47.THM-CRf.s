%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:08 EST 2020

% Result     : Theorem 2.92s
% Output     : CNFRefutation 3.00s
% Verified   : 
% Statistics : Number of formulae       :   66 (  82 expanded)
%              Number of leaves         :   27 (  38 expanded)
%              Depth                    :    8
%              Number of atoms          :   94 ( 133 expanded)
%              Number of equality atoms :   30 (  50 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_xboole_0 > v1_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_86,negated_conjecture,(
    ~ ! [A,B] :
        ~ ( A != k1_xboole_0
          & B != k1_xboole_0
          & ~ ( k1_relat_1(k2_zfmisc_1(A,B)) = A
              & k2_relat_1(k2_zfmisc_1(A,B)) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t195_relat_1)).

tff(f_65,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_73,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => r1_tarski(A,k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_relat_1)).

tff(f_60,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B,C,D] :
          ( ( r1_tarski(k2_zfmisc_1(A,B),k2_zfmisc_1(C,D))
            | r1_tarski(k2_zfmisc_1(B,A),k2_zfmisc_1(D,C)) )
         => r1_tarski(B,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_zfmisc_1)).

tff(f_69,axiom,(
    ! [A,B] : r1_tarski(k2_relat_1(k2_zfmisc_1(A,B)),B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t194_relat_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_67,axiom,(
    ! [A,B] : r1_tarski(k1_relat_1(k2_zfmisc_1(A,B)),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t193_relat_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
        <=> r2_hidden(C,B) )
     => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tarski)).

tff(f_50,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_63,axiom,(
    ! [A,B] : ~ r2_hidden(A,k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(c_44,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_32,plain,(
    ! [A_21,B_22] : v1_relat_1(k2_zfmisc_1(A_21,B_22)) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_38,plain,(
    ! [A_27] :
      ( r1_tarski(A_27,k2_zfmisc_1(k1_relat_1(A_27),k2_relat_1(A_27)))
      | ~ v1_relat_1(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_1004,plain,(
    ! [A_128,B_129,C_130,D_131] :
      ( ~ r1_tarski(k2_zfmisc_1(A_128,B_129),k2_zfmisc_1(C_130,D_131))
      | r1_tarski(B_129,D_131)
      | v1_xboole_0(A_128) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_1011,plain,(
    ! [B_129,A_128] :
      ( r1_tarski(B_129,k2_relat_1(k2_zfmisc_1(A_128,B_129)))
      | v1_xboole_0(A_128)
      | ~ v1_relat_1(k2_zfmisc_1(A_128,B_129)) ) ),
    inference(resolution,[status(thm)],[c_38,c_1004])).

tff(c_1038,plain,(
    ! [B_132,A_133] :
      ( r1_tarski(B_132,k2_relat_1(k2_zfmisc_1(A_133,B_132)))
      | v1_xboole_0(A_133) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_1011])).

tff(c_36,plain,(
    ! [A_25,B_26] : r1_tarski(k2_relat_1(k2_zfmisc_1(A_25,B_26)),B_26) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_647,plain,(
    ! [B_102,A_103] :
      ( B_102 = A_103
      | ~ r1_tarski(B_102,A_103)
      | ~ r1_tarski(A_103,B_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_661,plain,(
    ! [A_25,B_26] :
      ( k2_relat_1(k2_zfmisc_1(A_25,B_26)) = B_26
      | ~ r1_tarski(B_26,k2_relat_1(k2_zfmisc_1(A_25,B_26))) ) ),
    inference(resolution,[status(thm)],[c_36,c_647])).

tff(c_1056,plain,(
    ! [A_134,B_135] :
      ( k2_relat_1(k2_zfmisc_1(A_134,B_135)) = B_135
      | v1_xboole_0(A_134) ) ),
    inference(resolution,[status(thm)],[c_1038,c_661])).

tff(c_42,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_34,plain,(
    ! [A_23,B_24] : r1_tarski(k1_relat_1(k2_zfmisc_1(A_23,B_24)),A_23) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_231,plain,(
    ! [B_53,A_54,D_55,C_56] :
      ( ~ r1_tarski(k2_zfmisc_1(B_53,A_54),k2_zfmisc_1(D_55,C_56))
      | r1_tarski(B_53,D_55)
      | v1_xboole_0(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_235,plain,(
    ! [B_53,A_54] :
      ( r1_tarski(B_53,k1_relat_1(k2_zfmisc_1(B_53,A_54)))
      | v1_xboole_0(A_54)
      | ~ v1_relat_1(k2_zfmisc_1(B_53,A_54)) ) ),
    inference(resolution,[status(thm)],[c_38,c_231])).

tff(c_284,plain,(
    ! [B_60,A_61] :
      ( r1_tarski(B_60,k1_relat_1(k2_zfmisc_1(B_60,A_61)))
      | v1_xboole_0(A_61) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_235])).

tff(c_14,plain,(
    ! [B_9,A_8] :
      ( B_9 = A_8
      | ~ r1_tarski(B_9,A_8)
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_286,plain,(
    ! [B_60,A_61] :
      ( k1_relat_1(k2_zfmisc_1(B_60,A_61)) = B_60
      | ~ r1_tarski(k1_relat_1(k2_zfmisc_1(B_60,A_61)),B_60)
      | v1_xboole_0(A_61) ) ),
    inference(resolution,[status(thm)],[c_284,c_14])).

tff(c_402,plain,(
    ! [B_70,A_71] :
      ( k1_relat_1(k2_zfmisc_1(B_70,A_71)) = B_70
      | v1_xboole_0(A_71) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_286])).

tff(c_40,plain,
    ( k2_relat_1(k2_zfmisc_1('#skF_4','#skF_5')) != '#skF_5'
    | k1_relat_1(k2_zfmisc_1('#skF_4','#skF_5')) != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_76,plain,(
    k1_relat_1(k2_zfmisc_1('#skF_4','#skF_5')) != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_432,plain,(
    v1_xboole_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_402,c_76])).

tff(c_552,plain,(
    ! [A_88,B_89] :
      ( r2_hidden('#skF_2'(A_88,B_89),B_89)
      | r2_hidden('#skF_3'(A_88,B_89),A_88)
      | B_89 = A_88 ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_22,plain,(
    ! [A_10] : k2_zfmisc_1(A_10,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_77,plain,(
    ! [A_35,B_36] : ~ r2_hidden(A_35,k2_zfmisc_1(A_35,B_36)) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_80,plain,(
    ! [A_10] : ~ r2_hidden(A_10,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_77])).

tff(c_575,plain,(
    ! [B_90] :
      ( r2_hidden('#skF_2'(k1_xboole_0,B_90),B_90)
      | k1_xboole_0 = B_90 ) ),
    inference(resolution,[status(thm)],[c_552,c_80])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_590,plain,(
    ! [B_91] :
      ( ~ v1_xboole_0(B_91)
      | k1_xboole_0 = B_91 ) ),
    inference(resolution,[status(thm)],[c_575,c_2])).

tff(c_593,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_432,c_590])).

tff(c_600,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_593])).

tff(c_601,plain,(
    k2_relat_1(k2_zfmisc_1('#skF_4','#skF_5')) != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_1100,plain,(
    v1_xboole_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1056,c_601])).

tff(c_1137,plain,(
    ! [A_143,B_144] :
      ( r2_hidden('#skF_2'(A_143,B_144),B_144)
      | r2_hidden('#skF_3'(A_143,B_144),A_143)
      | B_144 = A_143 ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_603,plain,(
    ! [A_92,B_93] : ~ r2_hidden(A_92,k2_zfmisc_1(A_92,B_93)) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_606,plain,(
    ! [A_10] : ~ r2_hidden(A_10,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_603])).

tff(c_1160,plain,(
    ! [B_145] :
      ( r2_hidden('#skF_2'(k1_xboole_0,B_145),B_145)
      | k1_xboole_0 = B_145 ) ),
    inference(resolution,[status(thm)],[c_1137,c_606])).

tff(c_1175,plain,(
    ! [B_146] :
      ( ~ v1_xboole_0(B_146)
      | k1_xboole_0 = B_146 ) ),
    inference(resolution,[status(thm)],[c_1160,c_2])).

tff(c_1178,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_1100,c_1175])).

tff(c_1185,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_1178])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:24:27 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.92/1.49  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.00/1.49  
% 3.00/1.49  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.00/1.49  %$ r2_hidden > r1_tarski > v1_xboole_0 > v1_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_4 > #skF_2
% 3.00/1.49  
% 3.00/1.49  %Foreground sorts:
% 3.00/1.49  
% 3.00/1.49  
% 3.00/1.49  %Background operators:
% 3.00/1.49  
% 3.00/1.49  
% 3.00/1.49  %Foreground operators:
% 3.00/1.49  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.00/1.49  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.00/1.49  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.00/1.49  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.00/1.49  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.00/1.49  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.00/1.49  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.00/1.49  tff('#skF_5', type, '#skF_5': $i).
% 3.00/1.49  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.00/1.49  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.00/1.49  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.00/1.49  tff('#skF_4', type, '#skF_4': $i).
% 3.00/1.49  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.00/1.49  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.00/1.49  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.00/1.49  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.00/1.50  
% 3.00/1.51  tff(f_86, negated_conjecture, ~(![A, B]: ~((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~((k1_relat_1(k2_zfmisc_1(A, B)) = A) & (k2_relat_1(k2_zfmisc_1(A, B)) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t195_relat_1)).
% 3.00/1.51  tff(f_65, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.00/1.51  tff(f_73, axiom, (![A]: (v1_relat_1(A) => r1_tarski(A, k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_relat_1)).
% 3.00/1.51  tff(f_60, axiom, (![A]: (~v1_xboole_0(A) => (![B, C, D]: ((r1_tarski(k2_zfmisc_1(A, B), k2_zfmisc_1(C, D)) | r1_tarski(k2_zfmisc_1(B, A), k2_zfmisc_1(D, C))) => r1_tarski(B, D))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t139_zfmisc_1)).
% 3.00/1.51  tff(f_69, axiom, (![A, B]: r1_tarski(k2_relat_1(k2_zfmisc_1(A, B)), B)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t194_relat_1)).
% 3.00/1.51  tff(f_44, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.00/1.51  tff(f_67, axiom, (![A, B]: r1_tarski(k1_relat_1(k2_zfmisc_1(A, B)), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t193_relat_1)).
% 3.00/1.51  tff(f_38, axiom, (![A, B]: ((![C]: (r2_hidden(C, A) <=> r2_hidden(C, B))) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_tarski)).
% 3.00/1.51  tff(f_50, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 3.00/1.51  tff(f_63, axiom, (![A, B]: ~r2_hidden(A, k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 3.00/1.51  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 3.00/1.51  tff(c_44, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.00/1.51  tff(c_32, plain, (![A_21, B_22]: (v1_relat_1(k2_zfmisc_1(A_21, B_22)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.00/1.51  tff(c_38, plain, (![A_27]: (r1_tarski(A_27, k2_zfmisc_1(k1_relat_1(A_27), k2_relat_1(A_27))) | ~v1_relat_1(A_27))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.00/1.51  tff(c_1004, plain, (![A_128, B_129, C_130, D_131]: (~r1_tarski(k2_zfmisc_1(A_128, B_129), k2_zfmisc_1(C_130, D_131)) | r1_tarski(B_129, D_131) | v1_xboole_0(A_128))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.00/1.51  tff(c_1011, plain, (![B_129, A_128]: (r1_tarski(B_129, k2_relat_1(k2_zfmisc_1(A_128, B_129))) | v1_xboole_0(A_128) | ~v1_relat_1(k2_zfmisc_1(A_128, B_129)))), inference(resolution, [status(thm)], [c_38, c_1004])).
% 3.00/1.51  tff(c_1038, plain, (![B_132, A_133]: (r1_tarski(B_132, k2_relat_1(k2_zfmisc_1(A_133, B_132))) | v1_xboole_0(A_133))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_1011])).
% 3.00/1.51  tff(c_36, plain, (![A_25, B_26]: (r1_tarski(k2_relat_1(k2_zfmisc_1(A_25, B_26)), B_26))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.00/1.51  tff(c_647, plain, (![B_102, A_103]: (B_102=A_103 | ~r1_tarski(B_102, A_103) | ~r1_tarski(A_103, B_102))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.00/1.51  tff(c_661, plain, (![A_25, B_26]: (k2_relat_1(k2_zfmisc_1(A_25, B_26))=B_26 | ~r1_tarski(B_26, k2_relat_1(k2_zfmisc_1(A_25, B_26))))), inference(resolution, [status(thm)], [c_36, c_647])).
% 3.00/1.51  tff(c_1056, plain, (![A_134, B_135]: (k2_relat_1(k2_zfmisc_1(A_134, B_135))=B_135 | v1_xboole_0(A_134))), inference(resolution, [status(thm)], [c_1038, c_661])).
% 3.00/1.51  tff(c_42, plain, (k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.00/1.51  tff(c_34, plain, (![A_23, B_24]: (r1_tarski(k1_relat_1(k2_zfmisc_1(A_23, B_24)), A_23))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.00/1.51  tff(c_231, plain, (![B_53, A_54, D_55, C_56]: (~r1_tarski(k2_zfmisc_1(B_53, A_54), k2_zfmisc_1(D_55, C_56)) | r1_tarski(B_53, D_55) | v1_xboole_0(A_54))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.00/1.51  tff(c_235, plain, (![B_53, A_54]: (r1_tarski(B_53, k1_relat_1(k2_zfmisc_1(B_53, A_54))) | v1_xboole_0(A_54) | ~v1_relat_1(k2_zfmisc_1(B_53, A_54)))), inference(resolution, [status(thm)], [c_38, c_231])).
% 3.00/1.51  tff(c_284, plain, (![B_60, A_61]: (r1_tarski(B_60, k1_relat_1(k2_zfmisc_1(B_60, A_61))) | v1_xboole_0(A_61))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_235])).
% 3.00/1.51  tff(c_14, plain, (![B_9, A_8]: (B_9=A_8 | ~r1_tarski(B_9, A_8) | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.00/1.51  tff(c_286, plain, (![B_60, A_61]: (k1_relat_1(k2_zfmisc_1(B_60, A_61))=B_60 | ~r1_tarski(k1_relat_1(k2_zfmisc_1(B_60, A_61)), B_60) | v1_xboole_0(A_61))), inference(resolution, [status(thm)], [c_284, c_14])).
% 3.00/1.51  tff(c_402, plain, (![B_70, A_71]: (k1_relat_1(k2_zfmisc_1(B_70, A_71))=B_70 | v1_xboole_0(A_71))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_286])).
% 3.00/1.51  tff(c_40, plain, (k2_relat_1(k2_zfmisc_1('#skF_4', '#skF_5'))!='#skF_5' | k1_relat_1(k2_zfmisc_1('#skF_4', '#skF_5'))!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.00/1.51  tff(c_76, plain, (k1_relat_1(k2_zfmisc_1('#skF_4', '#skF_5'))!='#skF_4'), inference(splitLeft, [status(thm)], [c_40])).
% 3.00/1.51  tff(c_432, plain, (v1_xboole_0('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_402, c_76])).
% 3.00/1.51  tff(c_552, plain, (![A_88, B_89]: (r2_hidden('#skF_2'(A_88, B_89), B_89) | r2_hidden('#skF_3'(A_88, B_89), A_88) | B_89=A_88)), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.00/1.51  tff(c_22, plain, (![A_10]: (k2_zfmisc_1(A_10, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.00/1.51  tff(c_77, plain, (![A_35, B_36]: (~r2_hidden(A_35, k2_zfmisc_1(A_35, B_36)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.00/1.51  tff(c_80, plain, (![A_10]: (~r2_hidden(A_10, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_22, c_77])).
% 3.00/1.51  tff(c_575, plain, (![B_90]: (r2_hidden('#skF_2'(k1_xboole_0, B_90), B_90) | k1_xboole_0=B_90)), inference(resolution, [status(thm)], [c_552, c_80])).
% 3.00/1.51  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.00/1.51  tff(c_590, plain, (![B_91]: (~v1_xboole_0(B_91) | k1_xboole_0=B_91)), inference(resolution, [status(thm)], [c_575, c_2])).
% 3.00/1.51  tff(c_593, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_432, c_590])).
% 3.00/1.51  tff(c_600, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_593])).
% 3.00/1.51  tff(c_601, plain, (k2_relat_1(k2_zfmisc_1('#skF_4', '#skF_5'))!='#skF_5'), inference(splitRight, [status(thm)], [c_40])).
% 3.00/1.51  tff(c_1100, plain, (v1_xboole_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1056, c_601])).
% 3.00/1.51  tff(c_1137, plain, (![A_143, B_144]: (r2_hidden('#skF_2'(A_143, B_144), B_144) | r2_hidden('#skF_3'(A_143, B_144), A_143) | B_144=A_143)), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.00/1.51  tff(c_603, plain, (![A_92, B_93]: (~r2_hidden(A_92, k2_zfmisc_1(A_92, B_93)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.00/1.51  tff(c_606, plain, (![A_10]: (~r2_hidden(A_10, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_22, c_603])).
% 3.00/1.51  tff(c_1160, plain, (![B_145]: (r2_hidden('#skF_2'(k1_xboole_0, B_145), B_145) | k1_xboole_0=B_145)), inference(resolution, [status(thm)], [c_1137, c_606])).
% 3.00/1.51  tff(c_1175, plain, (![B_146]: (~v1_xboole_0(B_146) | k1_xboole_0=B_146)), inference(resolution, [status(thm)], [c_1160, c_2])).
% 3.00/1.51  tff(c_1178, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_1100, c_1175])).
% 3.00/1.51  tff(c_1185, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_1178])).
% 3.00/1.51  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.00/1.51  
% 3.00/1.51  Inference rules
% 3.00/1.51  ----------------------
% 3.00/1.51  #Ref     : 0
% 3.00/1.51  #Sup     : 241
% 3.00/1.51  #Fact    : 0
% 3.00/1.51  #Define  : 0
% 3.00/1.51  #Split   : 4
% 3.00/1.51  #Chain   : 0
% 3.00/1.51  #Close   : 0
% 3.00/1.51  
% 3.00/1.51  Ordering : KBO
% 3.00/1.51  
% 3.00/1.51  Simplification rules
% 3.00/1.51  ----------------------
% 3.00/1.51  #Subsume      : 24
% 3.00/1.51  #Demod        : 220
% 3.00/1.51  #Tautology    : 160
% 3.00/1.51  #SimpNegUnit  : 2
% 3.00/1.51  #BackRed      : 17
% 3.00/1.51  
% 3.00/1.51  #Partial instantiations: 0
% 3.00/1.51  #Strategies tried      : 1
% 3.00/1.51  
% 3.00/1.51  Timing (in seconds)
% 3.00/1.51  ----------------------
% 3.00/1.51  Preprocessing        : 0.32
% 3.00/1.51  Parsing              : 0.18
% 3.00/1.51  CNF conversion       : 0.02
% 3.00/1.51  Main loop            : 0.39
% 3.00/1.51  Inferencing          : 0.15
% 3.00/1.51  Reduction            : 0.13
% 3.00/1.51  Demodulation         : 0.09
% 3.00/1.51  BG Simplification    : 0.02
% 3.00/1.51  Subsumption          : 0.06
% 3.00/1.51  Abstraction          : 0.02
% 3.00/1.51  MUC search           : 0.00
% 3.00/1.51  Cooper               : 0.00
% 3.00/1.51  Total                : 0.74
% 3.00/1.51  Index Insertion      : 0.00
% 3.00/1.51  Index Deletion       : 0.00
% 3.00/1.51  Index Matching       : 0.00
% 3.00/1.51  BG Taut test         : 0.00
%------------------------------------------------------------------------------
