%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:16 EST 2020

% Result     : Theorem 2.28s
% Output     : CNFRefutation 2.58s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 100 expanded)
%              Number of leaves         :   31 (  48 expanded)
%              Depth                    :   10
%              Number of atoms          :   96 ( 154 expanded)
%              Number of equality atoms :   38 (  73 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_93,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ( k5_relat_1(k1_xboole_0,A) = k1_xboole_0
          & k5_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_relat_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_63,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k5_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).

tff(f_33,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_86,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_74,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k1_relat_1(k5_relat_1(A,B)),k1_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_relat_1)).

tff(f_35,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_67,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k3_xboole_0(A,k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A))) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_relat_1)).

tff(f_83,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(k1_relat_1(A),k2_relat_1(B))
           => k2_relat_1(k5_relat_1(B,A)) = k2_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_relat_1)).

tff(c_46,plain,
    ( k5_relat_1('#skF_1',k1_xboole_0) != k1_xboole_0
    | k5_relat_1(k1_xboole_0,'#skF_1') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_77,plain,(
    k5_relat_1(k1_xboole_0,'#skF_1') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_48,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_61,plain,(
    ! [A_51] : k2_zfmisc_1(A_51,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_34,plain,(
    ! [A_38,B_39] : v1_relat_1(k2_zfmisc_1(A_38,B_39)) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_65,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_61,c_34])).

tff(c_32,plain,(
    ! [A_36,B_37] :
      ( v1_relat_1(k5_relat_1(A_36,B_37))
      | ~ v1_relat_1(B_37)
      | ~ v1_relat_1(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_8,plain,(
    ! [A_3] : k3_xboole_0(A_3,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_28,plain,(
    ! [B_33] : k2_zfmisc_1(k1_xboole_0,B_33) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_44,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_186,plain,(
    ! [A_73,B_74] :
      ( r1_tarski(k1_relat_1(k5_relat_1(A_73,B_74)),k1_relat_1(A_73))
      | ~ v1_relat_1(B_74)
      | ~ v1_relat_1(A_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_191,plain,(
    ! [B_74] :
      ( r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,B_74)),k1_xboole_0)
      | ~ v1_relat_1(B_74)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_186])).

tff(c_195,plain,(
    ! [B_75] :
      ( r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,B_75)),k1_xboole_0)
      | ~ v1_relat_1(B_75) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_191])).

tff(c_10,plain,(
    ! [A_4] : r1_tarski(k1_xboole_0,A_4) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_125,plain,(
    ! [B_60,A_61] :
      ( B_60 = A_61
      | ~ r1_tarski(B_60,A_61)
      | ~ r1_tarski(A_61,B_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_134,plain,(
    ! [A_4] :
      ( k1_xboole_0 = A_4
      | ~ r1_tarski(A_4,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_10,c_125])).

tff(c_205,plain,(
    ! [B_76] :
      ( k1_relat_1(k5_relat_1(k1_xboole_0,B_76)) = k1_xboole_0
      | ~ v1_relat_1(B_76) ) ),
    inference(resolution,[status(thm)],[c_195,c_134])).

tff(c_36,plain,(
    ! [A_40] :
      ( k3_xboole_0(A_40,k2_zfmisc_1(k1_relat_1(A_40),k2_relat_1(A_40))) = A_40
      | ~ v1_relat_1(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_220,plain,(
    ! [B_76] :
      ( k3_xboole_0(k5_relat_1(k1_xboole_0,B_76),k2_zfmisc_1(k1_xboole_0,k2_relat_1(k5_relat_1(k1_xboole_0,B_76)))) = k5_relat_1(k1_xboole_0,B_76)
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_76))
      | ~ v1_relat_1(B_76) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_205,c_36])).

tff(c_239,plain,(
    ! [B_82] :
      ( k5_relat_1(k1_xboole_0,B_82) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_82))
      | ~ v1_relat_1(B_82) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_28,c_220])).

tff(c_243,plain,(
    ! [B_37] :
      ( k5_relat_1(k1_xboole_0,B_37) = k1_xboole_0
      | ~ v1_relat_1(B_37)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_32,c_239])).

tff(c_247,plain,(
    ! [B_83] :
      ( k5_relat_1(k1_xboole_0,B_83) = k1_xboole_0
      | ~ v1_relat_1(B_83) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_243])).

tff(c_259,plain,(
    k5_relat_1(k1_xboole_0,'#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_48,c_247])).

tff(c_266,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_77,c_259])).

tff(c_267,plain,(
    k5_relat_1('#skF_1',k1_xboole_0) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_26,plain,(
    ! [A_32] : k2_zfmisc_1(A_32,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_42,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_603,plain,(
    ! [B_125,A_126] :
      ( k2_relat_1(k5_relat_1(B_125,A_126)) = k2_relat_1(A_126)
      | ~ r1_tarski(k1_relat_1(A_126),k2_relat_1(B_125))
      | ~ v1_relat_1(B_125)
      | ~ v1_relat_1(A_126) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_609,plain,(
    ! [B_125] :
      ( k2_relat_1(k5_relat_1(B_125,k1_xboole_0)) = k2_relat_1(k1_xboole_0)
      | ~ r1_tarski(k1_xboole_0,k2_relat_1(B_125))
      | ~ v1_relat_1(B_125)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_603])).

tff(c_619,plain,(
    ! [B_127] :
      ( k2_relat_1(k5_relat_1(B_127,k1_xboole_0)) = k1_xboole_0
      | ~ v1_relat_1(B_127) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_10,c_42,c_609])).

tff(c_628,plain,(
    ! [B_127] :
      ( k3_xboole_0(k5_relat_1(B_127,k1_xboole_0),k2_zfmisc_1(k1_relat_1(k5_relat_1(B_127,k1_xboole_0)),k1_xboole_0)) = k5_relat_1(B_127,k1_xboole_0)
      | ~ v1_relat_1(k5_relat_1(B_127,k1_xboole_0))
      | ~ v1_relat_1(B_127) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_619,c_36])).

tff(c_640,plain,(
    ! [B_128] :
      ( k5_relat_1(B_128,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(B_128,k1_xboole_0))
      | ~ v1_relat_1(B_128) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_26,c_628])).

tff(c_647,plain,(
    ! [A_36] :
      ( k5_relat_1(A_36,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_36) ) ),
    inference(resolution,[status(thm)],[c_32,c_640])).

tff(c_653,plain,(
    ! [A_129] :
      ( k5_relat_1(A_129,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_129) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_647])).

tff(c_665,plain,(
    k5_relat_1('#skF_1',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_48,c_653])).

tff(c_673,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_267,c_665])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.33  % Computer   : n002.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:24:21 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.28/1.30  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.28/1.31  
% 2.28/1.31  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.28/1.31  %$ r1_tarski > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_1
% 2.28/1.31  
% 2.28/1.31  %Foreground sorts:
% 2.28/1.31  
% 2.28/1.31  
% 2.28/1.31  %Background operators:
% 2.28/1.31  
% 2.28/1.31  
% 2.28/1.31  %Foreground operators:
% 2.28/1.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.28/1.31  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.28/1.31  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.28/1.31  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.28/1.31  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.28/1.31  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.28/1.31  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.28/1.31  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.28/1.31  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.28/1.31  tff('#skF_1', type, '#skF_1': $i).
% 2.28/1.31  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.28/1.31  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.28/1.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.28/1.31  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.28/1.31  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.28/1.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.28/1.31  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.28/1.31  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.28/1.31  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.28/1.31  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.28/1.31  
% 2.58/1.33  tff(f_93, negated_conjecture, ~(![A]: (v1_relat_1(A) => ((k5_relat_1(k1_xboole_0, A) = k1_xboole_0) & (k5_relat_1(A, k1_xboole_0) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_relat_1)).
% 2.58/1.33  tff(f_53, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.58/1.33  tff(f_63, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.58/1.33  tff(f_61, axiom, (![A, B]: ((v1_relat_1(A) & v1_relat_1(B)) => v1_relat_1(k5_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 2.58/1.33  tff(f_33, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 2.58/1.33  tff(f_86, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 2.58/1.33  tff(f_74, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k5_relat_1(A, B)), k1_relat_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_relat_1)).
% 2.58/1.33  tff(f_35, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.58/1.33  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.58/1.33  tff(f_67, axiom, (![A]: (v1_relat_1(A) => (k3_xboole_0(A, k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_relat_1)).
% 2.58/1.33  tff(f_83, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(A), k2_relat_1(B)) => (k2_relat_1(k5_relat_1(B, A)) = k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_relat_1)).
% 2.58/1.33  tff(c_46, plain, (k5_relat_1('#skF_1', k1_xboole_0)!=k1_xboole_0 | k5_relat_1(k1_xboole_0, '#skF_1')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.58/1.33  tff(c_77, plain, (k5_relat_1(k1_xboole_0, '#skF_1')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_46])).
% 2.58/1.33  tff(c_48, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.58/1.33  tff(c_61, plain, (![A_51]: (k2_zfmisc_1(A_51, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.58/1.33  tff(c_34, plain, (![A_38, B_39]: (v1_relat_1(k2_zfmisc_1(A_38, B_39)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.58/1.33  tff(c_65, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_61, c_34])).
% 2.58/1.33  tff(c_32, plain, (![A_36, B_37]: (v1_relat_1(k5_relat_1(A_36, B_37)) | ~v1_relat_1(B_37) | ~v1_relat_1(A_36))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.58/1.33  tff(c_8, plain, (![A_3]: (k3_xboole_0(A_3, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.58/1.33  tff(c_28, plain, (![B_33]: (k2_zfmisc_1(k1_xboole_0, B_33)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.58/1.33  tff(c_44, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.58/1.33  tff(c_186, plain, (![A_73, B_74]: (r1_tarski(k1_relat_1(k5_relat_1(A_73, B_74)), k1_relat_1(A_73)) | ~v1_relat_1(B_74) | ~v1_relat_1(A_73))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.58/1.33  tff(c_191, plain, (![B_74]: (r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0, B_74)), k1_xboole_0) | ~v1_relat_1(B_74) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_44, c_186])).
% 2.58/1.33  tff(c_195, plain, (![B_75]: (r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0, B_75)), k1_xboole_0) | ~v1_relat_1(B_75))), inference(demodulation, [status(thm), theory('equality')], [c_65, c_191])).
% 2.58/1.33  tff(c_10, plain, (![A_4]: (r1_tarski(k1_xboole_0, A_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.58/1.33  tff(c_125, plain, (![B_60, A_61]: (B_60=A_61 | ~r1_tarski(B_60, A_61) | ~r1_tarski(A_61, B_60))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.58/1.33  tff(c_134, plain, (![A_4]: (k1_xboole_0=A_4 | ~r1_tarski(A_4, k1_xboole_0))), inference(resolution, [status(thm)], [c_10, c_125])).
% 2.58/1.33  tff(c_205, plain, (![B_76]: (k1_relat_1(k5_relat_1(k1_xboole_0, B_76))=k1_xboole_0 | ~v1_relat_1(B_76))), inference(resolution, [status(thm)], [c_195, c_134])).
% 2.58/1.33  tff(c_36, plain, (![A_40]: (k3_xboole_0(A_40, k2_zfmisc_1(k1_relat_1(A_40), k2_relat_1(A_40)))=A_40 | ~v1_relat_1(A_40))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.58/1.33  tff(c_220, plain, (![B_76]: (k3_xboole_0(k5_relat_1(k1_xboole_0, B_76), k2_zfmisc_1(k1_xboole_0, k2_relat_1(k5_relat_1(k1_xboole_0, B_76))))=k5_relat_1(k1_xboole_0, B_76) | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_76)) | ~v1_relat_1(B_76))), inference(superposition, [status(thm), theory('equality')], [c_205, c_36])).
% 2.58/1.33  tff(c_239, plain, (![B_82]: (k5_relat_1(k1_xboole_0, B_82)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_82)) | ~v1_relat_1(B_82))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_28, c_220])).
% 2.58/1.33  tff(c_243, plain, (![B_37]: (k5_relat_1(k1_xboole_0, B_37)=k1_xboole_0 | ~v1_relat_1(B_37) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_32, c_239])).
% 2.58/1.33  tff(c_247, plain, (![B_83]: (k5_relat_1(k1_xboole_0, B_83)=k1_xboole_0 | ~v1_relat_1(B_83))), inference(demodulation, [status(thm), theory('equality')], [c_65, c_243])).
% 2.58/1.33  tff(c_259, plain, (k5_relat_1(k1_xboole_0, '#skF_1')=k1_xboole_0), inference(resolution, [status(thm)], [c_48, c_247])).
% 2.58/1.33  tff(c_266, plain, $false, inference(negUnitSimplification, [status(thm)], [c_77, c_259])).
% 2.58/1.33  tff(c_267, plain, (k5_relat_1('#skF_1', k1_xboole_0)!=k1_xboole_0), inference(splitRight, [status(thm)], [c_46])).
% 2.58/1.33  tff(c_26, plain, (![A_32]: (k2_zfmisc_1(A_32, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.58/1.33  tff(c_42, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.58/1.33  tff(c_603, plain, (![B_125, A_126]: (k2_relat_1(k5_relat_1(B_125, A_126))=k2_relat_1(A_126) | ~r1_tarski(k1_relat_1(A_126), k2_relat_1(B_125)) | ~v1_relat_1(B_125) | ~v1_relat_1(A_126))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.58/1.33  tff(c_609, plain, (![B_125]: (k2_relat_1(k5_relat_1(B_125, k1_xboole_0))=k2_relat_1(k1_xboole_0) | ~r1_tarski(k1_xboole_0, k2_relat_1(B_125)) | ~v1_relat_1(B_125) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_44, c_603])).
% 2.58/1.33  tff(c_619, plain, (![B_127]: (k2_relat_1(k5_relat_1(B_127, k1_xboole_0))=k1_xboole_0 | ~v1_relat_1(B_127))), inference(demodulation, [status(thm), theory('equality')], [c_65, c_10, c_42, c_609])).
% 2.58/1.33  tff(c_628, plain, (![B_127]: (k3_xboole_0(k5_relat_1(B_127, k1_xboole_0), k2_zfmisc_1(k1_relat_1(k5_relat_1(B_127, k1_xboole_0)), k1_xboole_0))=k5_relat_1(B_127, k1_xboole_0) | ~v1_relat_1(k5_relat_1(B_127, k1_xboole_0)) | ~v1_relat_1(B_127))), inference(superposition, [status(thm), theory('equality')], [c_619, c_36])).
% 2.58/1.33  tff(c_640, plain, (![B_128]: (k5_relat_1(B_128, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(B_128, k1_xboole_0)) | ~v1_relat_1(B_128))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_26, c_628])).
% 2.58/1.33  tff(c_647, plain, (![A_36]: (k5_relat_1(A_36, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_36))), inference(resolution, [status(thm)], [c_32, c_640])).
% 2.58/1.33  tff(c_653, plain, (![A_129]: (k5_relat_1(A_129, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_129))), inference(demodulation, [status(thm), theory('equality')], [c_65, c_647])).
% 2.58/1.33  tff(c_665, plain, (k5_relat_1('#skF_1', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_48, c_653])).
% 2.58/1.33  tff(c_673, plain, $false, inference(negUnitSimplification, [status(thm)], [c_267, c_665])).
% 2.58/1.33  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.58/1.33  
% 2.58/1.33  Inference rules
% 2.58/1.33  ----------------------
% 2.58/1.33  #Ref     : 0
% 2.58/1.33  #Sup     : 137
% 2.58/1.33  #Fact    : 0
% 2.58/1.33  #Define  : 0
% 2.58/1.33  #Split   : 1
% 2.58/1.33  #Chain   : 0
% 2.58/1.33  #Close   : 0
% 2.58/1.33  
% 2.58/1.33  Ordering : KBO
% 2.58/1.33  
% 2.58/1.33  Simplification rules
% 2.58/1.33  ----------------------
% 2.58/1.33  #Subsume      : 5
% 2.58/1.33  #Demod        : 118
% 2.58/1.33  #Tautology    : 105
% 2.58/1.33  #SimpNegUnit  : 2
% 2.58/1.33  #BackRed      : 0
% 2.58/1.33  
% 2.58/1.33  #Partial instantiations: 0
% 2.58/1.33  #Strategies tried      : 1
% 2.58/1.33  
% 2.58/1.33  Timing (in seconds)
% 2.58/1.33  ----------------------
% 2.58/1.33  Preprocessing        : 0.32
% 2.58/1.33  Parsing              : 0.17
% 2.58/1.33  CNF conversion       : 0.02
% 2.58/1.33  Main loop            : 0.25
% 2.58/1.33  Inferencing          : 0.10
% 2.58/1.33  Reduction            : 0.08
% 2.58/1.33  Demodulation         : 0.06
% 2.58/1.33  BG Simplification    : 0.02
% 2.58/1.33  Subsumption          : 0.04
% 2.58/1.33  Abstraction          : 0.02
% 2.58/1.33  MUC search           : 0.00
% 2.58/1.33  Cooper               : 0.00
% 2.58/1.33  Total                : 0.61
% 2.58/1.33  Index Insertion      : 0.00
% 2.58/1.33  Index Deletion       : 0.00
% 2.58/1.33  Index Matching       : 0.00
% 2.58/1.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
