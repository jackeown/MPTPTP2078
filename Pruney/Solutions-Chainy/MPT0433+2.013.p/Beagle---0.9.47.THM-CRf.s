%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:15 EST 2020

% Result     : Theorem 4.45s
% Output     : CNFRefutation 4.76s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 125 expanded)
%              Number of leaves         :   28 (  54 expanded)
%              Depth                    :   10
%              Number of atoms          :   99 ( 185 expanded)
%              Number of equality atoms :   14 (  36 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > v1_relat_1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_77,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => r1_tarski(k1_relat_1(k3_xboole_0(A,B)),k3_xboole_0(k1_relat_1(A),k1_relat_1(B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_41,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_62,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_69,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k1_relat_1(k2_xboole_0(A,B)) = k2_xboole_0(k1_relat_1(A),k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_relat_1)).

tff(f_43,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C) )
     => r1_tarski(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).

tff(c_32,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_125,plain,(
    ! [A_52,B_53] : k4_xboole_0(A_52,k4_xboole_0(A_52,B_53)) = k3_xboole_0(A_52,B_53) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_8,plain,(
    ! [A_8,B_9] : r1_tarski(k4_xboole_0(A_8,B_9),A_8) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_137,plain,(
    ! [A_52,B_53] : r1_tarski(k3_xboole_0(A_52,B_53),A_52) ),
    inference(superposition,[status(thm),theory(equality)],[c_125,c_8])).

tff(c_24,plain,(
    ! [A_23,B_24] :
      ( m1_subset_1(A_23,k1_zfmisc_1(B_24))
      | ~ r1_tarski(A_23,B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_157,plain,(
    ! [B_56,A_57] :
      ( v1_relat_1(B_56)
      | ~ m1_subset_1(B_56,k1_zfmisc_1(A_57))
      | ~ v1_relat_1(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_238,plain,(
    ! [A_67,B_68] :
      ( v1_relat_1(A_67)
      | ~ v1_relat_1(B_68)
      | ~ r1_tarski(A_67,B_68) ) ),
    inference(resolution,[status(thm)],[c_24,c_157])).

tff(c_274,plain,(
    ! [A_72,B_73] :
      ( v1_relat_1(k3_xboole_0(A_72,B_73))
      | ~ v1_relat_1(A_72) ) ),
    inference(resolution,[status(thm)],[c_137,c_238])).

tff(c_277,plain,(
    ! [B_2,A_1] :
      ( v1_relat_1(k3_xboole_0(B_2,A_1))
      | ~ v1_relat_1(A_1) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_274])).

tff(c_10,plain,(
    ! [A_10,B_11] : k4_xboole_0(A_10,k4_xboole_0(A_10,B_11)) = k3_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_70,plain,(
    ! [A_38,B_39] :
      ( k2_xboole_0(A_38,B_39) = B_39
      | ~ r1_tarski(A_38,B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_77,plain,(
    ! [A_8,B_9] : k2_xboole_0(k4_xboole_0(A_8,B_9),A_8) = A_8 ),
    inference(resolution,[status(thm)],[c_8,c_70])).

tff(c_1810,plain,(
    ! [A_137,B_138] :
      ( k2_xboole_0(k1_relat_1(A_137),k1_relat_1(B_138)) = k1_relat_1(k2_xboole_0(A_137,B_138))
      | ~ v1_relat_1(B_138)
      | ~ v1_relat_1(A_137) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_12,plain,(
    ! [A_12,B_13] : r1_tarski(A_12,k2_xboole_0(A_12,B_13)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1925,plain,(
    ! [A_143,B_144] :
      ( r1_tarski(k1_relat_1(A_143),k1_relat_1(k2_xboole_0(A_143,B_144)))
      | ~ v1_relat_1(B_144)
      | ~ v1_relat_1(A_143) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1810,c_12])).

tff(c_2702,plain,(
    ! [A_175,B_176] :
      ( r1_tarski(k1_relat_1(k4_xboole_0(A_175,B_176)),k1_relat_1(A_175))
      | ~ v1_relat_1(A_175)
      | ~ v1_relat_1(k4_xboole_0(A_175,B_176)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_77,c_1925])).

tff(c_2723,plain,(
    ! [A_10,B_11] :
      ( r1_tarski(k1_relat_1(k3_xboole_0(A_10,B_11)),k1_relat_1(A_10))
      | ~ v1_relat_1(A_10)
      | ~ v1_relat_1(k4_xboole_0(A_10,k4_xboole_0(A_10,B_11))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_2702])).

tff(c_3225,plain,(
    ! [A_186,B_187] :
      ( r1_tarski(k1_relat_1(k3_xboole_0(A_186,B_187)),k1_relat_1(A_186))
      | ~ v1_relat_1(A_186)
      | ~ v1_relat_1(k3_xboole_0(A_186,B_187)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_2723])).

tff(c_3246,plain,(
    ! [B_188,A_189] :
      ( r1_tarski(k1_relat_1(k3_xboole_0(B_188,A_189)),k1_relat_1(A_189))
      | ~ v1_relat_1(A_189)
      | ~ v1_relat_1(k3_xboole_0(A_189,B_188)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_3225])).

tff(c_34,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_146,plain,(
    ! [A_54,B_55] : r1_tarski(k3_xboole_0(A_54,B_55),A_54) ),
    inference(superposition,[status(thm),theory(equality)],[c_125,c_8])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( k2_xboole_0(A_3,B_4) = B_4
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_156,plain,(
    ! [A_54,B_55] : k2_xboole_0(k3_xboole_0(A_54,B_55),A_54) = A_54 ),
    inference(resolution,[status(thm)],[c_146,c_4])).

tff(c_78,plain,(
    ! [A_12,B_13] : k2_xboole_0(A_12,k2_xboole_0(A_12,B_13)) = k2_xboole_0(A_12,B_13) ),
    inference(resolution,[status(thm)],[c_12,c_70])).

tff(c_303,plain,(
    ! [A_80,B_81] :
      ( k2_xboole_0(k1_relat_1(A_80),k1_relat_1(B_81)) = k1_relat_1(k2_xboole_0(A_80,B_81))
      | ~ v1_relat_1(B_81)
      | ~ v1_relat_1(A_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_429,plain,(
    ! [A_88,B_89] :
      ( r1_tarski(k1_relat_1(A_88),k1_relat_1(k2_xboole_0(A_88,B_89)))
      | ~ v1_relat_1(B_89)
      | ~ v1_relat_1(A_88) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_303,c_12])).

tff(c_1183,plain,(
    ! [A_120,B_121] :
      ( r1_tarski(k1_relat_1(A_120),k1_relat_1(k2_xboole_0(A_120,B_121)))
      | ~ v1_relat_1(k2_xboole_0(A_120,B_121))
      | ~ v1_relat_1(A_120) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_78,c_429])).

tff(c_1213,plain,(
    ! [A_54,B_55] :
      ( r1_tarski(k1_relat_1(k3_xboole_0(A_54,B_55)),k1_relat_1(A_54))
      | ~ v1_relat_1(k2_xboole_0(k3_xboole_0(A_54,B_55),A_54))
      | ~ v1_relat_1(k3_xboole_0(A_54,B_55)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_156,c_1183])).

tff(c_1574,plain,(
    ! [A_128,B_129] :
      ( r1_tarski(k1_relat_1(k3_xboole_0(A_128,B_129)),k1_relat_1(A_128))
      | ~ v1_relat_1(A_128)
      | ~ v1_relat_1(k3_xboole_0(A_128,B_129)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_156,c_1213])).

tff(c_255,plain,(
    ! [A_69,B_70,C_71] :
      ( r1_tarski(A_69,k3_xboole_0(B_70,C_71))
      | ~ r1_tarski(A_69,C_71)
      | ~ r1_tarski(A_69,B_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_30,plain,(
    ~ r1_tarski(k1_relat_1(k3_xboole_0('#skF_1','#skF_2')),k3_xboole_0(k1_relat_1('#skF_1'),k1_relat_1('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_272,plain,
    ( ~ r1_tarski(k1_relat_1(k3_xboole_0('#skF_1','#skF_2')),k1_relat_1('#skF_2'))
    | ~ r1_tarski(k1_relat_1(k3_xboole_0('#skF_1','#skF_2')),k1_relat_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_255,c_30])).

tff(c_295,plain,(
    ~ r1_tarski(k1_relat_1(k3_xboole_0('#skF_1','#skF_2')),k1_relat_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_272])).

tff(c_1577,plain,
    ( ~ v1_relat_1('#skF_1')
    | ~ v1_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_1574,c_295])).

tff(c_1598,plain,(
    ~ v1_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_1577])).

tff(c_1748,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_277,c_1598])).

tff(c_1755,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_1748])).

tff(c_1756,plain,(
    ~ r1_tarski(k1_relat_1(k3_xboole_0('#skF_1','#skF_2')),k1_relat_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_272])).

tff(c_3249,plain,
    ( ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1(k3_xboole_0('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_3246,c_1756])).

tff(c_3270,plain,(
    ~ v1_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_32,c_3249])).

tff(c_3277,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_277,c_3270])).

tff(c_3284,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_3277])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:03:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.45/2.22  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.45/2.23  
% 4.45/2.23  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.45/2.23  %$ r1_tarski > m1_subset_1 > v1_relat_1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1
% 4.45/2.23  
% 4.45/2.23  %Foreground sorts:
% 4.45/2.23  
% 4.45/2.23  
% 4.45/2.23  %Background operators:
% 4.45/2.23  
% 4.45/2.23  
% 4.45/2.23  %Foreground operators:
% 4.45/2.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.45/2.23  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.45/2.23  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.45/2.23  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.45/2.23  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.45/2.23  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.45/2.23  tff('#skF_2', type, '#skF_2': $i).
% 4.45/2.23  tff('#skF_1', type, '#skF_1': $i).
% 4.45/2.23  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.45/2.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.45/2.23  tff(k3_tarski, type, k3_tarski: $i > $i).
% 4.45/2.23  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.45/2.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.45/2.23  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.45/2.23  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.45/2.23  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.45/2.23  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.45/2.23  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 4.45/2.23  
% 4.76/2.24  tff(f_77, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k3_xboole_0(A, B)), k3_xboole_0(k1_relat_1(A), k1_relat_1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_relat_1)).
% 4.76/2.24  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 4.76/2.24  tff(f_41, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 4.76/2.24  tff(f_39, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 4.76/2.24  tff(f_55, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 4.76/2.24  tff(f_62, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 4.76/2.24  tff(f_31, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 4.76/2.24  tff(f_69, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k1_relat_1(k2_xboole_0(A, B)) = k2_xboole_0(k1_relat_1(A), k1_relat_1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_relat_1)).
% 4.76/2.24  tff(f_43, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 4.76/2.24  tff(f_37, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(A, C)) => r1_tarski(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_xboole_1)).
% 4.76/2.24  tff(c_32, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.76/2.24  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.76/2.24  tff(c_125, plain, (![A_52, B_53]: (k4_xboole_0(A_52, k4_xboole_0(A_52, B_53))=k3_xboole_0(A_52, B_53))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.76/2.24  tff(c_8, plain, (![A_8, B_9]: (r1_tarski(k4_xboole_0(A_8, B_9), A_8))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.76/2.24  tff(c_137, plain, (![A_52, B_53]: (r1_tarski(k3_xboole_0(A_52, B_53), A_52))), inference(superposition, [status(thm), theory('equality')], [c_125, c_8])).
% 4.76/2.24  tff(c_24, plain, (![A_23, B_24]: (m1_subset_1(A_23, k1_zfmisc_1(B_24)) | ~r1_tarski(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.76/2.24  tff(c_157, plain, (![B_56, A_57]: (v1_relat_1(B_56) | ~m1_subset_1(B_56, k1_zfmisc_1(A_57)) | ~v1_relat_1(A_57))), inference(cnfTransformation, [status(thm)], [f_62])).
% 4.76/2.24  tff(c_238, plain, (![A_67, B_68]: (v1_relat_1(A_67) | ~v1_relat_1(B_68) | ~r1_tarski(A_67, B_68))), inference(resolution, [status(thm)], [c_24, c_157])).
% 4.76/2.24  tff(c_274, plain, (![A_72, B_73]: (v1_relat_1(k3_xboole_0(A_72, B_73)) | ~v1_relat_1(A_72))), inference(resolution, [status(thm)], [c_137, c_238])).
% 4.76/2.24  tff(c_277, plain, (![B_2, A_1]: (v1_relat_1(k3_xboole_0(B_2, A_1)) | ~v1_relat_1(A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_274])).
% 4.76/2.24  tff(c_10, plain, (![A_10, B_11]: (k4_xboole_0(A_10, k4_xboole_0(A_10, B_11))=k3_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.76/2.24  tff(c_70, plain, (![A_38, B_39]: (k2_xboole_0(A_38, B_39)=B_39 | ~r1_tarski(A_38, B_39))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.76/2.24  tff(c_77, plain, (![A_8, B_9]: (k2_xboole_0(k4_xboole_0(A_8, B_9), A_8)=A_8)), inference(resolution, [status(thm)], [c_8, c_70])).
% 4.76/2.24  tff(c_1810, plain, (![A_137, B_138]: (k2_xboole_0(k1_relat_1(A_137), k1_relat_1(B_138))=k1_relat_1(k2_xboole_0(A_137, B_138)) | ~v1_relat_1(B_138) | ~v1_relat_1(A_137))), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.76/2.24  tff(c_12, plain, (![A_12, B_13]: (r1_tarski(A_12, k2_xboole_0(A_12, B_13)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.76/2.24  tff(c_1925, plain, (![A_143, B_144]: (r1_tarski(k1_relat_1(A_143), k1_relat_1(k2_xboole_0(A_143, B_144))) | ~v1_relat_1(B_144) | ~v1_relat_1(A_143))), inference(superposition, [status(thm), theory('equality')], [c_1810, c_12])).
% 4.76/2.24  tff(c_2702, plain, (![A_175, B_176]: (r1_tarski(k1_relat_1(k4_xboole_0(A_175, B_176)), k1_relat_1(A_175)) | ~v1_relat_1(A_175) | ~v1_relat_1(k4_xboole_0(A_175, B_176)))), inference(superposition, [status(thm), theory('equality')], [c_77, c_1925])).
% 4.76/2.24  tff(c_2723, plain, (![A_10, B_11]: (r1_tarski(k1_relat_1(k3_xboole_0(A_10, B_11)), k1_relat_1(A_10)) | ~v1_relat_1(A_10) | ~v1_relat_1(k4_xboole_0(A_10, k4_xboole_0(A_10, B_11))))), inference(superposition, [status(thm), theory('equality')], [c_10, c_2702])).
% 4.76/2.24  tff(c_3225, plain, (![A_186, B_187]: (r1_tarski(k1_relat_1(k3_xboole_0(A_186, B_187)), k1_relat_1(A_186)) | ~v1_relat_1(A_186) | ~v1_relat_1(k3_xboole_0(A_186, B_187)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_2723])).
% 4.76/2.24  tff(c_3246, plain, (![B_188, A_189]: (r1_tarski(k1_relat_1(k3_xboole_0(B_188, A_189)), k1_relat_1(A_189)) | ~v1_relat_1(A_189) | ~v1_relat_1(k3_xboole_0(A_189, B_188)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_3225])).
% 4.76/2.24  tff(c_34, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.76/2.24  tff(c_146, plain, (![A_54, B_55]: (r1_tarski(k3_xboole_0(A_54, B_55), A_54))), inference(superposition, [status(thm), theory('equality')], [c_125, c_8])).
% 4.76/2.24  tff(c_4, plain, (![A_3, B_4]: (k2_xboole_0(A_3, B_4)=B_4 | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.76/2.24  tff(c_156, plain, (![A_54, B_55]: (k2_xboole_0(k3_xboole_0(A_54, B_55), A_54)=A_54)), inference(resolution, [status(thm)], [c_146, c_4])).
% 4.76/2.24  tff(c_78, plain, (![A_12, B_13]: (k2_xboole_0(A_12, k2_xboole_0(A_12, B_13))=k2_xboole_0(A_12, B_13))), inference(resolution, [status(thm)], [c_12, c_70])).
% 4.76/2.24  tff(c_303, plain, (![A_80, B_81]: (k2_xboole_0(k1_relat_1(A_80), k1_relat_1(B_81))=k1_relat_1(k2_xboole_0(A_80, B_81)) | ~v1_relat_1(B_81) | ~v1_relat_1(A_80))), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.76/2.24  tff(c_429, plain, (![A_88, B_89]: (r1_tarski(k1_relat_1(A_88), k1_relat_1(k2_xboole_0(A_88, B_89))) | ~v1_relat_1(B_89) | ~v1_relat_1(A_88))), inference(superposition, [status(thm), theory('equality')], [c_303, c_12])).
% 4.76/2.24  tff(c_1183, plain, (![A_120, B_121]: (r1_tarski(k1_relat_1(A_120), k1_relat_1(k2_xboole_0(A_120, B_121))) | ~v1_relat_1(k2_xboole_0(A_120, B_121)) | ~v1_relat_1(A_120))), inference(superposition, [status(thm), theory('equality')], [c_78, c_429])).
% 4.76/2.24  tff(c_1213, plain, (![A_54, B_55]: (r1_tarski(k1_relat_1(k3_xboole_0(A_54, B_55)), k1_relat_1(A_54)) | ~v1_relat_1(k2_xboole_0(k3_xboole_0(A_54, B_55), A_54)) | ~v1_relat_1(k3_xboole_0(A_54, B_55)))), inference(superposition, [status(thm), theory('equality')], [c_156, c_1183])).
% 4.76/2.24  tff(c_1574, plain, (![A_128, B_129]: (r1_tarski(k1_relat_1(k3_xboole_0(A_128, B_129)), k1_relat_1(A_128)) | ~v1_relat_1(A_128) | ~v1_relat_1(k3_xboole_0(A_128, B_129)))), inference(demodulation, [status(thm), theory('equality')], [c_156, c_1213])).
% 4.76/2.24  tff(c_255, plain, (![A_69, B_70, C_71]: (r1_tarski(A_69, k3_xboole_0(B_70, C_71)) | ~r1_tarski(A_69, C_71) | ~r1_tarski(A_69, B_70))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.76/2.24  tff(c_30, plain, (~r1_tarski(k1_relat_1(k3_xboole_0('#skF_1', '#skF_2')), k3_xboole_0(k1_relat_1('#skF_1'), k1_relat_1('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.76/2.24  tff(c_272, plain, (~r1_tarski(k1_relat_1(k3_xboole_0('#skF_1', '#skF_2')), k1_relat_1('#skF_2')) | ~r1_tarski(k1_relat_1(k3_xboole_0('#skF_1', '#skF_2')), k1_relat_1('#skF_1'))), inference(resolution, [status(thm)], [c_255, c_30])).
% 4.76/2.24  tff(c_295, plain, (~r1_tarski(k1_relat_1(k3_xboole_0('#skF_1', '#skF_2')), k1_relat_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_272])).
% 4.76/2.24  tff(c_1577, plain, (~v1_relat_1('#skF_1') | ~v1_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_1574, c_295])).
% 4.76/2.24  tff(c_1598, plain, (~v1_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_1577])).
% 4.76/2.24  tff(c_1748, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_277, c_1598])).
% 4.76/2.24  tff(c_1755, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_1748])).
% 4.76/2.24  tff(c_1756, plain, (~r1_tarski(k1_relat_1(k3_xboole_0('#skF_1', '#skF_2')), k1_relat_1('#skF_2'))), inference(splitRight, [status(thm)], [c_272])).
% 4.76/2.24  tff(c_3249, plain, (~v1_relat_1('#skF_2') | ~v1_relat_1(k3_xboole_0('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_3246, c_1756])).
% 4.76/2.24  tff(c_3270, plain, (~v1_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_32, c_3249])).
% 4.76/2.24  tff(c_3277, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_277, c_3270])).
% 4.76/2.24  tff(c_3284, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_3277])).
% 4.76/2.24  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.76/2.24  
% 4.76/2.24  Inference rules
% 4.76/2.24  ----------------------
% 4.76/2.24  #Ref     : 0
% 4.76/2.24  #Sup     : 822
% 4.76/2.24  #Fact    : 0
% 4.76/2.24  #Define  : 0
% 4.76/2.24  #Split   : 2
% 4.76/2.24  #Chain   : 0
% 4.76/2.24  #Close   : 0
% 4.76/2.24  
% 4.76/2.24  Ordering : KBO
% 4.76/2.24  
% 4.76/2.24  Simplification rules
% 4.76/2.24  ----------------------
% 4.76/2.24  #Subsume      : 228
% 4.76/2.24  #Demod        : 390
% 4.76/2.24  #Tautology    : 298
% 4.76/2.24  #SimpNegUnit  : 0
% 4.76/2.24  #BackRed      : 0
% 4.76/2.24  
% 4.76/2.24  #Partial instantiations: 0
% 4.76/2.24  #Strategies tried      : 1
% 4.76/2.24  
% 4.76/2.24  Timing (in seconds)
% 4.76/2.24  ----------------------
% 4.76/2.25  Preprocessing        : 0.49
% 4.76/2.25  Parsing              : 0.26
% 4.76/2.25  CNF conversion       : 0.03
% 4.76/2.25  Main loop            : 0.83
% 4.76/2.25  Inferencing          : 0.27
% 4.76/2.25  Reduction            : 0.37
% 4.76/2.25  Demodulation         : 0.31
% 4.76/2.25  BG Simplification    : 0.04
% 4.76/2.25  Subsumption          : 0.12
% 4.76/2.25  Abstraction          : 0.05
% 4.76/2.25  MUC search           : 0.00
% 4.76/2.25  Cooper               : 0.00
% 4.76/2.25  Total                : 1.36
% 4.76/2.25  Index Insertion      : 0.00
% 4.76/2.25  Index Deletion       : 0.00
% 4.76/2.25  Index Matching       : 0.00
% 4.76/2.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------
