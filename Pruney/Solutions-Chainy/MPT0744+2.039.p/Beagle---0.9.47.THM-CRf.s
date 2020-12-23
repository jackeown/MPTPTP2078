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
% DateTime   : Thu Dec  3 10:06:20 EST 2020

% Result     : Theorem 15.39s
% Output     : CNFRefutation 15.65s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 111 expanded)
%              Number of leaves         :   26 (  49 expanded)
%              Depth                    :   10
%              Number of atoms          :  109 ( 227 expanded)
%              Number of equality atoms :   10 (  16 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > v2_ordinal1 > v1_ordinal1 > k2_xboole_0 > #nlpp > k1_tarski > k1_ordinal1 > #skF_5 > #skF_1 > #skF_7 > #skF_3 > #skF_6 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_5',type,(
    '#skF_5': $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(k1_ordinal1,type,(
    k1_ordinal1: $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(v1_ordinal1,type,(
    v1_ordinal1: $i > $o )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r1_ordinal1,type,(
    r1_ordinal1: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(v3_ordinal1,type,(
    v3_ordinal1: $i > $o )).

tff(v2_ordinal1,type,(
    v2_ordinal1: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_100,negated_conjecture,(
    ~ ! [A] :
        ( v3_ordinal1(A)
       => ! [B] :
            ( v3_ordinal1(B)
           => ( r2_hidden(A,k1_ordinal1(B))
            <=> r1_ordinal1(A,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_ordinal1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_70,axiom,(
    ! [A,B] :
      ( ( v3_ordinal1(A)
        & v3_ordinal1(B) )
     => ( r1_ordinal1(A,B)
      <=> r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

tff(f_76,axiom,(
    ! [A,B] :
      ( r2_hidden(A,k1_ordinal1(B))
    <=> ( r2_hidden(A,B)
        | A = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_ordinal1)).

tff(f_85,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ( r1_ordinal1(A,B)
            | r2_hidden(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_ordinal1)).

tff(f_53,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ( v1_ordinal1(A)
        & v2_ordinal1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_ordinal1)).

tff(f_62,axiom,(
    ! [A] :
      ( v1_ordinal1(A)
    <=> ! [B] :
          ( r2_hidden(B,A)
         => r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_ordinal1)).

tff(c_66,plain,(
    v3_ordinal1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_24,plain,(
    ! [B_8] : r1_tarski(B_8,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_34435,plain,(
    ! [A_10455,B_10456] :
      ( r1_ordinal1(A_10455,B_10456)
      | ~ r1_tarski(A_10455,B_10456)
      | ~ v3_ordinal1(B_10456)
      | ~ v3_ordinal1(A_10455) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_34452,plain,(
    ! [B_10457] :
      ( r1_ordinal1(B_10457,B_10457)
      | ~ v3_ordinal1(B_10457) ) ),
    inference(resolution,[status(thm)],[c_24,c_34435])).

tff(c_56,plain,(
    ! [B_23] : r2_hidden(B_23,k1_ordinal1(B_23)) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_64,plain,(
    v3_ordinal1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_74,plain,
    ( r2_hidden('#skF_6',k1_ordinal1('#skF_7'))
    | r1_ordinal1('#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_97,plain,(
    r1_ordinal1('#skF_6','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_74])).

tff(c_619,plain,(
    ! [B_106,A_107] :
      ( r2_hidden(B_106,A_107)
      | r1_ordinal1(A_107,B_106)
      | ~ v3_ordinal1(B_106)
      | ~ v3_ordinal1(A_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_138,plain,(
    ! [A_45,B_46] :
      ( ~ r2_hidden(A_45,B_46)
      | r2_hidden(A_45,k1_ordinal1(B_46)) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_68,plain,
    ( ~ r1_ordinal1('#skF_6','#skF_7')
    | ~ r2_hidden('#skF_6',k1_ordinal1('#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_125,plain,(
    ~ r2_hidden('#skF_6',k1_ordinal1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_68])).

tff(c_145,plain,(
    ~ r2_hidden('#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_138,c_125])).

tff(c_702,plain,
    ( r1_ordinal1('#skF_7','#skF_6')
    | ~ v3_ordinal1('#skF_6')
    | ~ v3_ordinal1('#skF_7') ),
    inference(resolution,[status(thm)],[c_619,c_145])).

tff(c_736,plain,(
    r1_ordinal1('#skF_7','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_66,c_702])).

tff(c_52,plain,(
    ! [A_20,B_21] :
      ( r1_tarski(A_20,B_21)
      | ~ r1_ordinal1(A_20,B_21)
      | ~ v3_ordinal1(B_21)
      | ~ v3_ordinal1(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_494,plain,(
    ! [A_92,B_93] :
      ( r1_tarski(A_92,B_93)
      | ~ r1_ordinal1(A_92,B_93)
      | ~ v3_ordinal1(B_93)
      | ~ v3_ordinal1(A_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_20,plain,(
    ! [B_8,A_7] :
      ( B_8 = A_7
      | ~ r1_tarski(B_8,A_7)
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_6401,plain,(
    ! [B_3346,A_3347] :
      ( B_3346 = A_3347
      | ~ r1_tarski(B_3346,A_3347)
      | ~ r1_ordinal1(A_3347,B_3346)
      | ~ v3_ordinal1(B_3346)
      | ~ v3_ordinal1(A_3347) ) ),
    inference(resolution,[status(thm)],[c_494,c_20])).

tff(c_33854,plain,(
    ! [B_10378,A_10379] :
      ( B_10378 = A_10379
      | ~ r1_ordinal1(B_10378,A_10379)
      | ~ r1_ordinal1(A_10379,B_10378)
      | ~ v3_ordinal1(B_10378)
      | ~ v3_ordinal1(A_10379) ) ),
    inference(resolution,[status(thm)],[c_52,c_6401])).

tff(c_33882,plain,
    ( '#skF_7' = '#skF_6'
    | ~ r1_ordinal1('#skF_6','#skF_7')
    | ~ v3_ordinal1('#skF_7')
    | ~ v3_ordinal1('#skF_6') ),
    inference(resolution,[status(thm)],[c_736,c_33854])).

tff(c_33901,plain,(
    '#skF_7' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_97,c_33882])).

tff(c_33913,plain,(
    ~ r2_hidden('#skF_6',k1_ordinal1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_33901,c_125])).

tff(c_33920,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_33913])).

tff(c_33922,plain,(
    ~ r1_ordinal1('#skF_6','#skF_7') ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_78,plain,(
    ! [A_32] :
      ( v1_ordinal1(A_32)
      | ~ v3_ordinal1(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_85,plain,(
    v1_ordinal1('#skF_7') ),
    inference(resolution,[status(thm)],[c_64,c_78])).

tff(c_33921,plain,(
    r2_hidden('#skF_6',k1_ordinal1('#skF_7')) ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_34227,plain,(
    ! [B_10439,A_10440] :
      ( B_10439 = A_10440
      | r2_hidden(A_10440,B_10439)
      | ~ r2_hidden(A_10440,k1_ordinal1(B_10439)) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_34243,plain,
    ( '#skF_7' = '#skF_6'
    | r2_hidden('#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_33921,c_34227])).

tff(c_34246,plain,(
    r2_hidden('#skF_6','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_34243])).

tff(c_44,plain,(
    ! [B_19,A_16] :
      ( r1_tarski(B_19,A_16)
      | ~ r2_hidden(B_19,A_16)
      | ~ v1_ordinal1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_34249,plain,
    ( r1_tarski('#skF_6','#skF_7')
    | ~ v1_ordinal1('#skF_7') ),
    inference(resolution,[status(thm)],[c_34246,c_44])).

tff(c_34255,plain,(
    r1_tarski('#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_34249])).

tff(c_34302,plain,(
    ! [A_10443,B_10444] :
      ( r1_ordinal1(A_10443,B_10444)
      | ~ r1_tarski(A_10443,B_10444)
      | ~ v3_ordinal1(B_10444)
      | ~ v3_ordinal1(A_10443) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_34308,plain,
    ( r1_ordinal1('#skF_6','#skF_7')
    | ~ v3_ordinal1('#skF_7')
    | ~ v3_ordinal1('#skF_6') ),
    inference(resolution,[status(thm)],[c_34255,c_34302])).

tff(c_34321,plain,(
    r1_ordinal1('#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_34308])).

tff(c_34323,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_33922,c_34321])).

tff(c_34324,plain,(
    '#skF_7' = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_34243])).

tff(c_34329,plain,(
    ~ r1_ordinal1('#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34324,c_33922])).

tff(c_34455,plain,(
    ~ v3_ordinal1('#skF_6') ),
    inference(resolution,[status(thm)],[c_34452,c_34329])).

tff(c_34459,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_34455])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 19:23:27 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 15.39/7.53  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.65/7.54  
% 15.65/7.54  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.65/7.54  %$ r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > v2_ordinal1 > v1_ordinal1 > k2_xboole_0 > #nlpp > k1_tarski > k1_ordinal1 > #skF_5 > #skF_1 > #skF_7 > #skF_3 > #skF_6 > #skF_2 > #skF_4
% 15.65/7.54  
% 15.65/7.54  %Foreground sorts:
% 15.65/7.54  
% 15.65/7.54  
% 15.65/7.54  %Background operators:
% 15.65/7.54  
% 15.65/7.54  
% 15.65/7.54  %Foreground operators:
% 15.65/7.54  tff('#skF_5', type, '#skF_5': $i > $i).
% 15.65/7.54  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 15.65/7.54  tff(k1_ordinal1, type, k1_ordinal1: $i > $i).
% 15.65/7.54  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 15.65/7.54  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 15.65/7.54  tff(k1_tarski, type, k1_tarski: $i > $i).
% 15.65/7.54  tff(v1_ordinal1, type, v1_ordinal1: $i > $o).
% 15.65/7.54  tff('#skF_7', type, '#skF_7': $i).
% 15.65/7.54  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 15.65/7.54  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 15.65/7.54  tff(r1_ordinal1, type, r1_ordinal1: ($i * $i) > $o).
% 15.65/7.54  tff('#skF_6', type, '#skF_6': $i).
% 15.65/7.54  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 15.65/7.54  tff(v3_ordinal1, type, v3_ordinal1: $i > $o).
% 15.65/7.54  tff(v2_ordinal1, type, v2_ordinal1: $i > $o).
% 15.65/7.54  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 15.65/7.54  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 15.65/7.54  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 15.65/7.54  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 15.65/7.54  
% 15.65/7.55  tff(f_100, negated_conjecture, ~(![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r2_hidden(A, k1_ordinal1(B)) <=> r1_ordinal1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_ordinal1)).
% 15.65/7.55  tff(f_40, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 15.65/7.55  tff(f_70, axiom, (![A, B]: ((v3_ordinal1(A) & v3_ordinal1(B)) => (r1_ordinal1(A, B) <=> r1_tarski(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r1_ordinal1)).
% 15.65/7.55  tff(f_76, axiom, (![A, B]: (r2_hidden(A, k1_ordinal1(B)) <=> (r2_hidden(A, B) | (A = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_ordinal1)).
% 15.65/7.55  tff(f_85, axiom, (![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r1_ordinal1(A, B) | r2_hidden(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_ordinal1)).
% 15.65/7.55  tff(f_53, axiom, (![A]: (v3_ordinal1(A) => (v1_ordinal1(A) & v2_ordinal1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_ordinal1)).
% 15.65/7.55  tff(f_62, axiom, (![A]: (v1_ordinal1(A) <=> (![B]: (r2_hidden(B, A) => r1_tarski(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_ordinal1)).
% 15.65/7.55  tff(c_66, plain, (v3_ordinal1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_100])).
% 15.65/7.55  tff(c_24, plain, (![B_8]: (r1_tarski(B_8, B_8))), inference(cnfTransformation, [status(thm)], [f_40])).
% 15.65/7.55  tff(c_34435, plain, (![A_10455, B_10456]: (r1_ordinal1(A_10455, B_10456) | ~r1_tarski(A_10455, B_10456) | ~v3_ordinal1(B_10456) | ~v3_ordinal1(A_10455))), inference(cnfTransformation, [status(thm)], [f_70])).
% 15.65/7.55  tff(c_34452, plain, (![B_10457]: (r1_ordinal1(B_10457, B_10457) | ~v3_ordinal1(B_10457))), inference(resolution, [status(thm)], [c_24, c_34435])).
% 15.65/7.55  tff(c_56, plain, (![B_23]: (r2_hidden(B_23, k1_ordinal1(B_23)))), inference(cnfTransformation, [status(thm)], [f_76])).
% 15.65/7.55  tff(c_64, plain, (v3_ordinal1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_100])).
% 15.65/7.55  tff(c_74, plain, (r2_hidden('#skF_6', k1_ordinal1('#skF_7')) | r1_ordinal1('#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_100])).
% 15.65/7.55  tff(c_97, plain, (r1_ordinal1('#skF_6', '#skF_7')), inference(splitLeft, [status(thm)], [c_74])).
% 15.65/7.55  tff(c_619, plain, (![B_106, A_107]: (r2_hidden(B_106, A_107) | r1_ordinal1(A_107, B_106) | ~v3_ordinal1(B_106) | ~v3_ordinal1(A_107))), inference(cnfTransformation, [status(thm)], [f_85])).
% 15.65/7.55  tff(c_138, plain, (![A_45, B_46]: (~r2_hidden(A_45, B_46) | r2_hidden(A_45, k1_ordinal1(B_46)))), inference(cnfTransformation, [status(thm)], [f_76])).
% 15.65/7.55  tff(c_68, plain, (~r1_ordinal1('#skF_6', '#skF_7') | ~r2_hidden('#skF_6', k1_ordinal1('#skF_7'))), inference(cnfTransformation, [status(thm)], [f_100])).
% 15.65/7.55  tff(c_125, plain, (~r2_hidden('#skF_6', k1_ordinal1('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_97, c_68])).
% 15.65/7.55  tff(c_145, plain, (~r2_hidden('#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_138, c_125])).
% 15.65/7.55  tff(c_702, plain, (r1_ordinal1('#skF_7', '#skF_6') | ~v3_ordinal1('#skF_6') | ~v3_ordinal1('#skF_7')), inference(resolution, [status(thm)], [c_619, c_145])).
% 15.65/7.55  tff(c_736, plain, (r1_ordinal1('#skF_7', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_66, c_702])).
% 15.65/7.55  tff(c_52, plain, (![A_20, B_21]: (r1_tarski(A_20, B_21) | ~r1_ordinal1(A_20, B_21) | ~v3_ordinal1(B_21) | ~v3_ordinal1(A_20))), inference(cnfTransformation, [status(thm)], [f_70])).
% 15.65/7.55  tff(c_494, plain, (![A_92, B_93]: (r1_tarski(A_92, B_93) | ~r1_ordinal1(A_92, B_93) | ~v3_ordinal1(B_93) | ~v3_ordinal1(A_92))), inference(cnfTransformation, [status(thm)], [f_70])).
% 15.65/7.55  tff(c_20, plain, (![B_8, A_7]: (B_8=A_7 | ~r1_tarski(B_8, A_7) | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_40])).
% 15.65/7.55  tff(c_6401, plain, (![B_3346, A_3347]: (B_3346=A_3347 | ~r1_tarski(B_3346, A_3347) | ~r1_ordinal1(A_3347, B_3346) | ~v3_ordinal1(B_3346) | ~v3_ordinal1(A_3347))), inference(resolution, [status(thm)], [c_494, c_20])).
% 15.65/7.55  tff(c_33854, plain, (![B_10378, A_10379]: (B_10378=A_10379 | ~r1_ordinal1(B_10378, A_10379) | ~r1_ordinal1(A_10379, B_10378) | ~v3_ordinal1(B_10378) | ~v3_ordinal1(A_10379))), inference(resolution, [status(thm)], [c_52, c_6401])).
% 15.65/7.55  tff(c_33882, plain, ('#skF_7'='#skF_6' | ~r1_ordinal1('#skF_6', '#skF_7') | ~v3_ordinal1('#skF_7') | ~v3_ordinal1('#skF_6')), inference(resolution, [status(thm)], [c_736, c_33854])).
% 15.65/7.55  tff(c_33901, plain, ('#skF_7'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_97, c_33882])).
% 15.65/7.55  tff(c_33913, plain, (~r2_hidden('#skF_6', k1_ordinal1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_33901, c_125])).
% 15.65/7.55  tff(c_33920, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_33913])).
% 15.65/7.55  tff(c_33922, plain, (~r1_ordinal1('#skF_6', '#skF_7')), inference(splitRight, [status(thm)], [c_74])).
% 15.65/7.55  tff(c_78, plain, (![A_32]: (v1_ordinal1(A_32) | ~v3_ordinal1(A_32))), inference(cnfTransformation, [status(thm)], [f_53])).
% 15.65/7.55  tff(c_85, plain, (v1_ordinal1('#skF_7')), inference(resolution, [status(thm)], [c_64, c_78])).
% 15.65/7.55  tff(c_33921, plain, (r2_hidden('#skF_6', k1_ordinal1('#skF_7'))), inference(splitRight, [status(thm)], [c_74])).
% 15.65/7.55  tff(c_34227, plain, (![B_10439, A_10440]: (B_10439=A_10440 | r2_hidden(A_10440, B_10439) | ~r2_hidden(A_10440, k1_ordinal1(B_10439)))), inference(cnfTransformation, [status(thm)], [f_76])).
% 15.65/7.55  tff(c_34243, plain, ('#skF_7'='#skF_6' | r2_hidden('#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_33921, c_34227])).
% 15.65/7.55  tff(c_34246, plain, (r2_hidden('#skF_6', '#skF_7')), inference(splitLeft, [status(thm)], [c_34243])).
% 15.65/7.55  tff(c_44, plain, (![B_19, A_16]: (r1_tarski(B_19, A_16) | ~r2_hidden(B_19, A_16) | ~v1_ordinal1(A_16))), inference(cnfTransformation, [status(thm)], [f_62])).
% 15.65/7.55  tff(c_34249, plain, (r1_tarski('#skF_6', '#skF_7') | ~v1_ordinal1('#skF_7')), inference(resolution, [status(thm)], [c_34246, c_44])).
% 15.65/7.55  tff(c_34255, plain, (r1_tarski('#skF_6', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_85, c_34249])).
% 15.65/7.55  tff(c_34302, plain, (![A_10443, B_10444]: (r1_ordinal1(A_10443, B_10444) | ~r1_tarski(A_10443, B_10444) | ~v3_ordinal1(B_10444) | ~v3_ordinal1(A_10443))), inference(cnfTransformation, [status(thm)], [f_70])).
% 15.65/7.55  tff(c_34308, plain, (r1_ordinal1('#skF_6', '#skF_7') | ~v3_ordinal1('#skF_7') | ~v3_ordinal1('#skF_6')), inference(resolution, [status(thm)], [c_34255, c_34302])).
% 15.65/7.55  tff(c_34321, plain, (r1_ordinal1('#skF_6', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_34308])).
% 15.65/7.55  tff(c_34323, plain, $false, inference(negUnitSimplification, [status(thm)], [c_33922, c_34321])).
% 15.65/7.55  tff(c_34324, plain, ('#skF_7'='#skF_6'), inference(splitRight, [status(thm)], [c_34243])).
% 15.65/7.55  tff(c_34329, plain, (~r1_ordinal1('#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_34324, c_33922])).
% 15.65/7.55  tff(c_34455, plain, (~v3_ordinal1('#skF_6')), inference(resolution, [status(thm)], [c_34452, c_34329])).
% 15.65/7.55  tff(c_34459, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_66, c_34455])).
% 15.65/7.55  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.65/7.55  
% 15.65/7.55  Inference rules
% 15.65/7.55  ----------------------
% 15.65/7.55  #Ref     : 0
% 15.65/7.55  #Sup     : 6824
% 15.65/7.55  #Fact    : 14
% 15.65/7.55  #Define  : 0
% 15.65/7.55  #Split   : 7
% 15.65/7.55  #Chain   : 0
% 15.65/7.55  #Close   : 0
% 15.65/7.55  
% 15.65/7.55  Ordering : KBO
% 15.65/7.55  
% 15.65/7.55  Simplification rules
% 15.65/7.55  ----------------------
% 15.65/7.55  #Subsume      : 2665
% 15.65/7.55  #Demod        : 228
% 15.65/7.55  #Tautology    : 213
% 15.65/7.55  #SimpNegUnit  : 98
% 15.65/7.55  #BackRed      : 24
% 15.65/7.55  
% 15.65/7.55  #Partial instantiations: 5840
% 15.65/7.55  #Strategies tried      : 1
% 15.65/7.55  
% 15.65/7.55  Timing (in seconds)
% 15.65/7.55  ----------------------
% 15.65/7.55  Preprocessing        : 0.30
% 15.65/7.55  Parsing              : 0.16
% 15.65/7.55  CNF conversion       : 0.03
% 15.65/7.56  Main loop            : 6.50
% 15.65/7.56  Inferencing          : 1.20
% 15.65/7.56  Reduction            : 1.96
% 15.65/7.56  Demodulation         : 0.67
% 15.65/7.56  BG Simplification    : 0.12
% 15.65/7.56  Subsumption          : 2.83
% 15.65/7.56  Abstraction          : 0.21
% 15.65/7.56  MUC search           : 0.00
% 15.65/7.56  Cooper               : 0.00
% 15.65/7.56  Total                : 6.83
% 15.65/7.56  Index Insertion      : 0.00
% 15.65/7.56  Index Deletion       : 0.00
% 15.65/7.56  Index Matching       : 0.00
% 15.65/7.56  BG Taut test         : 0.00
%------------------------------------------------------------------------------
