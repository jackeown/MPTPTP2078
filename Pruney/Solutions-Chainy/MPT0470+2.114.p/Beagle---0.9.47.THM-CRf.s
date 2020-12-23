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
% DateTime   : Thu Dec  3 09:59:16 EST 2020

% Result     : Theorem 2.48s
% Output     : CNFRefutation 2.73s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 123 expanded)
%              Number of leaves         :   36 (  55 expanded)
%              Depth                    :   13
%              Number of atoms          :  135 ( 207 expanded)
%              Number of equality atoms :   36 (  70 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > v1_relat_1 > k5_relat_1 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_5 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_125,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ( k5_relat_1(k1_xboole_0,A) = k1_xboole_0
          & k5_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_relat_1)).

tff(f_77,axiom,(
    ! [A] :
      ( v1_relat_1(A)
    <=> ! [B] :
          ~ ( r2_hidden(B,A)
            & ! [C,D] : B != k4_tarski(C,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_relat_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_67,axiom,(
    ! [A,B] : ~ r2_hidden(A,k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).

tff(f_83,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k5_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

tff(f_30,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_58,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_118,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_115,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(k2_relat_1(A),k1_relat_1(B))
           => k1_relat_1(k5_relat_1(A,B)) = k1_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_relat_1)).

tff(f_91,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_relat_1(A) )
     => ~ v1_xboole_0(k1_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc8_relat_1)).

tff(f_34,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_52,axiom,(
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

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_106,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k2_relat_1(k5_relat_1(A,B)),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_relat_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_99,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_relat_1(A) )
     => ~ v1_xboole_0(k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_relat_1)).

tff(c_48,plain,
    ( k5_relat_1('#skF_5',k1_xboole_0) != k1_xboole_0
    | k5_relat_1(k1_xboole_0,'#skF_5') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_95,plain,(
    k5_relat_1(k1_xboole_0,'#skF_5') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_50,plain,(
    v1_relat_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_97,plain,(
    ! [A_51] :
      ( r2_hidden('#skF_2'(A_51),A_51)
      | v1_relat_1(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_22,plain,(
    ! [A_12] : k2_zfmisc_1(A_12,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_88,plain,(
    ! [A_48,B_49] : ~ r2_hidden(A_48,k2_zfmisc_1(A_48,B_49)) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_94,plain,(
    ! [A_12] : ~ r2_hidden(A_12,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_88])).

tff(c_102,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_97,c_94])).

tff(c_34,plain,(
    ! [A_34,B_35] :
      ( v1_relat_1(k5_relat_1(A_34,B_35))
      | ~ v1_relat_1(B_35)
      | ~ v1_relat_1(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_18,plain,(
    ! [A_11] : r1_tarski(k1_xboole_0,A_11) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_46,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_44,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_282,plain,(
    ! [A_95,B_96] :
      ( k1_relat_1(k5_relat_1(A_95,B_96)) = k1_relat_1(A_95)
      | ~ r1_tarski(k2_relat_1(A_95),k1_relat_1(B_96))
      | ~ v1_relat_1(B_96)
      | ~ v1_relat_1(A_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_291,plain,(
    ! [B_96] :
      ( k1_relat_1(k5_relat_1(k1_xboole_0,B_96)) = k1_relat_1(k1_xboole_0)
      | ~ r1_tarski(k1_xboole_0,k1_relat_1(B_96))
      | ~ v1_relat_1(B_96)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_282])).

tff(c_298,plain,(
    ! [B_97] :
      ( k1_relat_1(k5_relat_1(k1_xboole_0,B_97)) = k1_xboole_0
      | ~ v1_relat_1(B_97) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_18,c_46,c_291])).

tff(c_36,plain,(
    ! [A_36] :
      ( ~ v1_xboole_0(k1_relat_1(A_36))
      | ~ v1_relat_1(A_36)
      | v1_xboole_0(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_307,plain,(
    ! [B_97] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_97))
      | v1_xboole_0(k5_relat_1(k1_xboole_0,B_97))
      | ~ v1_relat_1(B_97) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_298,c_36])).

tff(c_315,plain,(
    ! [B_98] :
      ( ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_98))
      | v1_xboole_0(k5_relat_1(k1_xboole_0,B_98))
      | ~ v1_relat_1(B_98) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_307])).

tff(c_8,plain,(
    ! [A_3] :
      ( k1_xboole_0 = A_3
      | ~ v1_xboole_0(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_325,plain,(
    ! [B_100] :
      ( k5_relat_1(k1_xboole_0,B_100) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_100))
      | ~ v1_relat_1(B_100) ) ),
    inference(resolution,[status(thm)],[c_315,c_8])).

tff(c_329,plain,(
    ! [B_35] :
      ( k5_relat_1(k1_xboole_0,B_35) = k1_xboole_0
      | ~ v1_relat_1(B_35)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_34,c_325])).

tff(c_333,plain,(
    ! [B_101] :
      ( k5_relat_1(k1_xboole_0,B_101) = k1_xboole_0
      | ~ v1_relat_1(B_101) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_329])).

tff(c_342,plain,(
    k5_relat_1(k1_xboole_0,'#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_50,c_333])).

tff(c_348,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_95,c_342])).

tff(c_349,plain,(
    k5_relat_1('#skF_5',k1_xboole_0) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_356,plain,(
    ! [A_103] :
      ( r2_hidden('#skF_2'(A_103),A_103)
      | v1_relat_1(A_103) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_361,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_356,c_94])).

tff(c_422,plain,(
    ! [A_123,B_124] :
      ( r2_hidden('#skF_1'(A_123,B_124),B_124)
      | r1_xboole_0(A_123,B_124) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_428,plain,(
    ! [A_125] : r1_xboole_0(A_125,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_422,c_94])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k3_xboole_0(A_1,B_2) = k1_xboole_0
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_432,plain,(
    ! [A_125] : k3_xboole_0(A_125,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_428,c_2])).

tff(c_484,plain,(
    ! [A_136,B_137] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_136,B_137)),k2_relat_1(B_137))
      | ~ v1_relat_1(B_137)
      | ~ v1_relat_1(A_136) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_493,plain,(
    ! [A_136] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_136,k1_xboole_0)),k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_136) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_484])).

tff(c_499,plain,(
    ! [A_138] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_138,k1_xboole_0)),k1_xboole_0)
      | ~ v1_relat_1(A_138) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_361,c_493])).

tff(c_16,plain,(
    ! [A_9,B_10] :
      ( k3_xboole_0(A_9,B_10) = A_9
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_502,plain,(
    ! [A_138] :
      ( k3_xboole_0(k2_relat_1(k5_relat_1(A_138,k1_xboole_0)),k1_xboole_0) = k2_relat_1(k5_relat_1(A_138,k1_xboole_0))
      | ~ v1_relat_1(A_138) ) ),
    inference(resolution,[status(thm)],[c_499,c_16])).

tff(c_505,plain,(
    ! [A_139] :
      ( k2_relat_1(k5_relat_1(A_139,k1_xboole_0)) = k1_xboole_0
      | ~ v1_relat_1(A_139) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_432,c_502])).

tff(c_38,plain,(
    ! [A_37] :
      ( ~ v1_xboole_0(k2_relat_1(A_37))
      | ~ v1_relat_1(A_37)
      | v1_xboole_0(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_520,plain,(
    ! [A_139] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ v1_relat_1(k5_relat_1(A_139,k1_xboole_0))
      | v1_xboole_0(k5_relat_1(A_139,k1_xboole_0))
      | ~ v1_relat_1(A_139) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_505,c_38])).

tff(c_531,plain,(
    ! [A_140] :
      ( ~ v1_relat_1(k5_relat_1(A_140,k1_xboole_0))
      | v1_xboole_0(k5_relat_1(A_140,k1_xboole_0))
      | ~ v1_relat_1(A_140) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_520])).

tff(c_536,plain,(
    ! [A_141] :
      ( k5_relat_1(A_141,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(A_141,k1_xboole_0))
      | ~ v1_relat_1(A_141) ) ),
    inference(resolution,[status(thm)],[c_531,c_8])).

tff(c_540,plain,(
    ! [A_34] :
      ( k5_relat_1(A_34,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_34) ) ),
    inference(resolution,[status(thm)],[c_34,c_536])).

tff(c_544,plain,(
    ! [A_142] :
      ( k5_relat_1(A_142,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_142) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_361,c_540])).

tff(c_553,plain,(
    k5_relat_1('#skF_5',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_50,c_544])).

tff(c_559,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_349,c_553])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n006.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 10:54:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.48/1.35  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.48/1.36  
% 2.48/1.36  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.73/1.36  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > v1_relat_1 > k5_relat_1 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_5 > #skF_1 > #skF_4
% 2.73/1.36  
% 2.73/1.36  %Foreground sorts:
% 2.73/1.36  
% 2.73/1.36  
% 2.73/1.36  %Background operators:
% 2.73/1.36  
% 2.73/1.36  
% 2.73/1.36  %Foreground operators:
% 2.73/1.36  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.73/1.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.73/1.36  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.73/1.36  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.73/1.36  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.73/1.36  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.73/1.36  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.73/1.36  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.73/1.36  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.73/1.36  tff('#skF_5', type, '#skF_5': $i).
% 2.73/1.36  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.73/1.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.73/1.36  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.73/1.36  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.73/1.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.73/1.36  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.73/1.36  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.73/1.36  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.73/1.36  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.73/1.36  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.73/1.36  
% 2.73/1.38  tff(f_125, negated_conjecture, ~(![A]: (v1_relat_1(A) => ((k5_relat_1(k1_xboole_0, A) = k1_xboole_0) & (k5_relat_1(A, k1_xboole_0) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_relat_1)).
% 2.73/1.38  tff(f_77, axiom, (![A]: (v1_relat_1(A) <=> (![B]: ~(r2_hidden(B, A) & (![C, D]: ~(B = k4_tarski(C, D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_relat_1)).
% 2.73/1.38  tff(f_64, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.73/1.38  tff(f_67, axiom, (![A, B]: ~r2_hidden(A, k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 2.73/1.38  tff(f_83, axiom, (![A, B]: ((v1_relat_1(A) & v1_relat_1(B)) => v1_relat_1(k5_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 2.73/1.38  tff(f_30, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.73/1.38  tff(f_58, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.73/1.38  tff(f_118, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 2.73/1.38  tff(f_115, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(A), k1_relat_1(B)) => (k1_relat_1(k5_relat_1(A, B)) = k1_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_relat_1)).
% 2.73/1.38  tff(f_91, axiom, (![A]: ((~v1_xboole_0(A) & v1_relat_1(A)) => ~v1_xboole_0(k1_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc8_relat_1)).
% 2.73/1.38  tff(f_34, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.73/1.38  tff(f_52, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 2.73/1.38  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 2.73/1.38  tff(f_106, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k5_relat_1(A, B)), k2_relat_1(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_relat_1)).
% 2.73/1.38  tff(f_56, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.73/1.38  tff(f_99, axiom, (![A]: ((~v1_xboole_0(A) & v1_relat_1(A)) => ~v1_xboole_0(k2_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc9_relat_1)).
% 2.73/1.38  tff(c_48, plain, (k5_relat_1('#skF_5', k1_xboole_0)!=k1_xboole_0 | k5_relat_1(k1_xboole_0, '#skF_5')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_125])).
% 2.73/1.38  tff(c_95, plain, (k5_relat_1(k1_xboole_0, '#skF_5')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_48])).
% 2.73/1.38  tff(c_50, plain, (v1_relat_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_125])).
% 2.73/1.38  tff(c_97, plain, (![A_51]: (r2_hidden('#skF_2'(A_51), A_51) | v1_relat_1(A_51))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.73/1.38  tff(c_22, plain, (![A_12]: (k2_zfmisc_1(A_12, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.73/1.38  tff(c_88, plain, (![A_48, B_49]: (~r2_hidden(A_48, k2_zfmisc_1(A_48, B_49)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.73/1.38  tff(c_94, plain, (![A_12]: (~r2_hidden(A_12, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_22, c_88])).
% 2.73/1.38  tff(c_102, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_97, c_94])).
% 2.73/1.38  tff(c_34, plain, (![A_34, B_35]: (v1_relat_1(k5_relat_1(A_34, B_35)) | ~v1_relat_1(B_35) | ~v1_relat_1(A_34))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.73/1.38  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_30])).
% 2.73/1.38  tff(c_18, plain, (![A_11]: (r1_tarski(k1_xboole_0, A_11))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.73/1.38  tff(c_46, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_118])).
% 2.73/1.38  tff(c_44, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_118])).
% 2.73/1.38  tff(c_282, plain, (![A_95, B_96]: (k1_relat_1(k5_relat_1(A_95, B_96))=k1_relat_1(A_95) | ~r1_tarski(k2_relat_1(A_95), k1_relat_1(B_96)) | ~v1_relat_1(B_96) | ~v1_relat_1(A_95))), inference(cnfTransformation, [status(thm)], [f_115])).
% 2.73/1.38  tff(c_291, plain, (![B_96]: (k1_relat_1(k5_relat_1(k1_xboole_0, B_96))=k1_relat_1(k1_xboole_0) | ~r1_tarski(k1_xboole_0, k1_relat_1(B_96)) | ~v1_relat_1(B_96) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_44, c_282])).
% 2.73/1.38  tff(c_298, plain, (![B_97]: (k1_relat_1(k5_relat_1(k1_xboole_0, B_97))=k1_xboole_0 | ~v1_relat_1(B_97))), inference(demodulation, [status(thm), theory('equality')], [c_102, c_18, c_46, c_291])).
% 2.73/1.38  tff(c_36, plain, (![A_36]: (~v1_xboole_0(k1_relat_1(A_36)) | ~v1_relat_1(A_36) | v1_xboole_0(A_36))), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.73/1.38  tff(c_307, plain, (![B_97]: (~v1_xboole_0(k1_xboole_0) | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_97)) | v1_xboole_0(k5_relat_1(k1_xboole_0, B_97)) | ~v1_relat_1(B_97))), inference(superposition, [status(thm), theory('equality')], [c_298, c_36])).
% 2.73/1.38  tff(c_315, plain, (![B_98]: (~v1_relat_1(k5_relat_1(k1_xboole_0, B_98)) | v1_xboole_0(k5_relat_1(k1_xboole_0, B_98)) | ~v1_relat_1(B_98))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_307])).
% 2.73/1.38  tff(c_8, plain, (![A_3]: (k1_xboole_0=A_3 | ~v1_xboole_0(A_3))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.73/1.38  tff(c_325, plain, (![B_100]: (k5_relat_1(k1_xboole_0, B_100)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_100)) | ~v1_relat_1(B_100))), inference(resolution, [status(thm)], [c_315, c_8])).
% 2.73/1.38  tff(c_329, plain, (![B_35]: (k5_relat_1(k1_xboole_0, B_35)=k1_xboole_0 | ~v1_relat_1(B_35) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_34, c_325])).
% 2.73/1.38  tff(c_333, plain, (![B_101]: (k5_relat_1(k1_xboole_0, B_101)=k1_xboole_0 | ~v1_relat_1(B_101))), inference(demodulation, [status(thm), theory('equality')], [c_102, c_329])).
% 2.73/1.38  tff(c_342, plain, (k5_relat_1(k1_xboole_0, '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_50, c_333])).
% 2.73/1.38  tff(c_348, plain, $false, inference(negUnitSimplification, [status(thm)], [c_95, c_342])).
% 2.73/1.38  tff(c_349, plain, (k5_relat_1('#skF_5', k1_xboole_0)!=k1_xboole_0), inference(splitRight, [status(thm)], [c_48])).
% 2.73/1.38  tff(c_356, plain, (![A_103]: (r2_hidden('#skF_2'(A_103), A_103) | v1_relat_1(A_103))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.73/1.38  tff(c_361, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_356, c_94])).
% 2.73/1.38  tff(c_422, plain, (![A_123, B_124]: (r2_hidden('#skF_1'(A_123, B_124), B_124) | r1_xboole_0(A_123, B_124))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.73/1.38  tff(c_428, plain, (![A_125]: (r1_xboole_0(A_125, k1_xboole_0))), inference(resolution, [status(thm)], [c_422, c_94])).
% 2.73/1.38  tff(c_2, plain, (![A_1, B_2]: (k3_xboole_0(A_1, B_2)=k1_xboole_0 | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.73/1.38  tff(c_432, plain, (![A_125]: (k3_xboole_0(A_125, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_428, c_2])).
% 2.73/1.38  tff(c_484, plain, (![A_136, B_137]: (r1_tarski(k2_relat_1(k5_relat_1(A_136, B_137)), k2_relat_1(B_137)) | ~v1_relat_1(B_137) | ~v1_relat_1(A_136))), inference(cnfTransformation, [status(thm)], [f_106])).
% 2.73/1.38  tff(c_493, plain, (![A_136]: (r1_tarski(k2_relat_1(k5_relat_1(A_136, k1_xboole_0)), k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_136))), inference(superposition, [status(thm), theory('equality')], [c_44, c_484])).
% 2.73/1.38  tff(c_499, plain, (![A_138]: (r1_tarski(k2_relat_1(k5_relat_1(A_138, k1_xboole_0)), k1_xboole_0) | ~v1_relat_1(A_138))), inference(demodulation, [status(thm), theory('equality')], [c_361, c_493])).
% 2.73/1.38  tff(c_16, plain, (![A_9, B_10]: (k3_xboole_0(A_9, B_10)=A_9 | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.73/1.38  tff(c_502, plain, (![A_138]: (k3_xboole_0(k2_relat_1(k5_relat_1(A_138, k1_xboole_0)), k1_xboole_0)=k2_relat_1(k5_relat_1(A_138, k1_xboole_0)) | ~v1_relat_1(A_138))), inference(resolution, [status(thm)], [c_499, c_16])).
% 2.73/1.38  tff(c_505, plain, (![A_139]: (k2_relat_1(k5_relat_1(A_139, k1_xboole_0))=k1_xboole_0 | ~v1_relat_1(A_139))), inference(demodulation, [status(thm), theory('equality')], [c_432, c_502])).
% 2.73/1.38  tff(c_38, plain, (![A_37]: (~v1_xboole_0(k2_relat_1(A_37)) | ~v1_relat_1(A_37) | v1_xboole_0(A_37))), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.73/1.38  tff(c_520, plain, (![A_139]: (~v1_xboole_0(k1_xboole_0) | ~v1_relat_1(k5_relat_1(A_139, k1_xboole_0)) | v1_xboole_0(k5_relat_1(A_139, k1_xboole_0)) | ~v1_relat_1(A_139))), inference(superposition, [status(thm), theory('equality')], [c_505, c_38])).
% 2.73/1.38  tff(c_531, plain, (![A_140]: (~v1_relat_1(k5_relat_1(A_140, k1_xboole_0)) | v1_xboole_0(k5_relat_1(A_140, k1_xboole_0)) | ~v1_relat_1(A_140))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_520])).
% 2.73/1.38  tff(c_536, plain, (![A_141]: (k5_relat_1(A_141, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(A_141, k1_xboole_0)) | ~v1_relat_1(A_141))), inference(resolution, [status(thm)], [c_531, c_8])).
% 2.73/1.38  tff(c_540, plain, (![A_34]: (k5_relat_1(A_34, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_34))), inference(resolution, [status(thm)], [c_34, c_536])).
% 2.73/1.38  tff(c_544, plain, (![A_142]: (k5_relat_1(A_142, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_142))), inference(demodulation, [status(thm), theory('equality')], [c_361, c_540])).
% 2.73/1.38  tff(c_553, plain, (k5_relat_1('#skF_5', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_50, c_544])).
% 2.73/1.38  tff(c_559, plain, $false, inference(negUnitSimplification, [status(thm)], [c_349, c_553])).
% 2.73/1.38  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.73/1.38  
% 2.73/1.38  Inference rules
% 2.73/1.38  ----------------------
% 2.73/1.38  #Ref     : 1
% 2.73/1.38  #Sup     : 109
% 2.73/1.38  #Fact    : 0
% 2.73/1.38  #Define  : 0
% 2.73/1.38  #Split   : 1
% 2.73/1.38  #Chain   : 0
% 2.73/1.38  #Close   : 0
% 2.73/1.38  
% 2.73/1.38  Ordering : KBO
% 2.73/1.38  
% 2.73/1.38  Simplification rules
% 2.73/1.38  ----------------------
% 2.73/1.38  #Subsume      : 8
% 2.73/1.38  #Demod        : 46
% 2.73/1.38  #Tautology    : 56
% 2.73/1.38  #SimpNegUnit  : 2
% 2.73/1.38  #BackRed      : 0
% 2.73/1.38  
% 2.73/1.38  #Partial instantiations: 0
% 2.73/1.38  #Strategies tried      : 1
% 2.73/1.38  
% 2.73/1.38  Timing (in seconds)
% 2.73/1.38  ----------------------
% 2.73/1.38  Preprocessing        : 0.32
% 2.73/1.38  Parsing              : 0.18
% 2.73/1.38  CNF conversion       : 0.02
% 2.73/1.38  Main loop            : 0.28
% 2.73/1.38  Inferencing          : 0.11
% 2.73/1.38  Reduction            : 0.07
% 2.73/1.38  Demodulation         : 0.05
% 2.73/1.38  BG Simplification    : 0.02
% 2.73/1.38  Subsumption          : 0.05
% 2.73/1.38  Abstraction          : 0.01
% 2.73/1.38  MUC search           : 0.00
% 2.73/1.38  Cooper               : 0.00
% 2.73/1.38  Total                : 0.64
% 2.73/1.38  Index Insertion      : 0.00
% 2.73/1.38  Index Deletion       : 0.00
% 2.73/1.38  Index Matching       : 0.00
% 2.73/1.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------
