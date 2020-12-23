%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:24 EST 2020

% Result     : Theorem 4.16s
% Output     : CNFRefutation 4.37s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 112 expanded)
%              Number of leaves         :   42 (  53 expanded)
%              Depth                    :   15
%              Number of atoms          :  111 ( 159 expanded)
%              Number of equality atoms :   46 (  60 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k2_subset_1 > k1_zfmisc_1 > k1_tarski > k1_subset_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k1_subset_1,type,(
    k1_subset_1: $i > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_68,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_72,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_84,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => k4_xboole_0(k2_xboole_0(A,B),B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_xboole_1)).

tff(f_70,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_147,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_123,axiom,(
    ! [A] : r1_tarski(k1_tarski(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_zfmisc_1)).

tff(f_86,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_121,axiom,(
    ! [A,B,C] :
      ( k4_xboole_0(A,k2_tarski(B,C)) = k1_xboole_0
    <=> ~ ( A != k1_xboole_0
          & A != k1_tarski(B)
          & A != k1_tarski(C)
          & A != k2_tarski(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_zfmisc_1)).

tff(f_106,axiom,(
    ! [A,B,C] :
      ( k4_xboole_0(k2_tarski(A,B),C) = k1_xboole_0
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_zfmisc_1)).

tff(f_34,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_136,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_144,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

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

tff(f_66,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_80,axiom,(
    ! [A,B,C,D] :
      ( ( k2_xboole_0(A,B) = k2_xboole_0(C,D)
        & r1_xboole_0(C,A)
        & r1_xboole_0(D,B) )
     => C = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_xboole_1)).

tff(f_151,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_138,axiom,(
    ! [A] : k1_subset_1(A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).

tff(f_140,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_154,negated_conjecture,(
    ~ ! [A] : k2_subset_1(A) = k3_subset_1(A,k1_subset_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_subset_1)).

tff(c_20,plain,(
    ! [A_18] : k2_xboole_0(A_18,k1_xboole_0) = A_18 ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_24,plain,(
    ! [A_21] : r1_xboole_0(A_21,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_461,plain,(
    ! [A_115,B_116] :
      ( k4_xboole_0(k2_xboole_0(A_115,B_116),B_116) = A_115
      | ~ r1_xboole_0(A_115,B_116) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_473,plain,(
    ! [A_18] :
      ( k4_xboole_0(A_18,k1_xboole_0) = A_18
      | ~ r1_xboole_0(A_18,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_461])).

tff(c_486,plain,(
    ! [A_117] : k4_xboole_0(A_117,k1_xboole_0) = A_117 ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_473])).

tff(c_22,plain,(
    ! [A_19,B_20] : k4_xboole_0(A_19,k4_xboole_0(A_19,B_20)) = k3_xboole_0(A_19,B_20) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_496,plain,(
    ! [A_117] : k4_xboole_0(A_117,A_117) = k3_xboole_0(A_117,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_486,c_22])).

tff(c_72,plain,(
    ! [A_48] : ~ v1_xboole_0(k1_zfmisc_1(A_48)) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_56,plain,(
    ! [A_41] : r1_tarski(k1_tarski(A_41),k1_zfmisc_1(A_41)) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_30,plain,(
    ! [A_28] : k2_tarski(A_28,A_28) = k1_tarski(A_28) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_48,plain,(
    ! [B_39,C_40] : k4_xboole_0(k2_tarski(B_39,C_40),k2_tarski(B_39,C_40)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_535,plain,(
    ! [B_121,C_122,A_123] :
      ( r2_hidden(B_121,C_122)
      | k4_xboole_0(k2_tarski(A_123,B_121),C_122) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_556,plain,(
    ! [C_126,B_127] : r2_hidden(C_126,k2_tarski(B_127,C_126)) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_535])).

tff(c_580,plain,(
    ! [A_131] : r2_hidden(A_131,k1_tarski(A_131)) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_556])).

tff(c_4,plain,(
    ! [C_7,B_4,A_3] :
      ( r2_hidden(C_7,B_4)
      | ~ r2_hidden(C_7,A_3)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_889,plain,(
    ! [A_153,B_154] :
      ( r2_hidden(A_153,B_154)
      | ~ r1_tarski(k1_tarski(A_153),B_154) ) ),
    inference(resolution,[status(thm)],[c_580,c_4])).

tff(c_900,plain,(
    ! [A_155] : r2_hidden(A_155,k1_zfmisc_1(A_155)) ),
    inference(resolution,[status(thm)],[c_56,c_889])).

tff(c_58,plain,(
    ! [B_43,A_42] :
      ( m1_subset_1(B_43,A_42)
      | ~ r2_hidden(B_43,A_42)
      | v1_xboole_0(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_905,plain,(
    ! [A_155] :
      ( m1_subset_1(A_155,k1_zfmisc_1(A_155))
      | v1_xboole_0(k1_zfmisc_1(A_155)) ) ),
    inference(resolution,[status(thm)],[c_900,c_58])).

tff(c_910,plain,(
    ! [A_156] : m1_subset_1(A_156,k1_zfmisc_1(A_156)) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_905])).

tff(c_70,plain,(
    ! [A_46,B_47] :
      ( k4_xboole_0(A_46,B_47) = k3_subset_1(A_46,B_47)
      | ~ m1_subset_1(B_47,k1_zfmisc_1(A_46)) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_922,plain,(
    ! [A_157] : k4_xboole_0(A_157,A_157) = k3_subset_1(A_157,A_157) ),
    inference(resolution,[status(thm)],[c_910,c_70])).

tff(c_1142,plain,(
    ! [A_166] : k3_xboole_0(A_166,k1_xboole_0) = k3_subset_1(A_166,A_166) ),
    inference(superposition,[status(thm),theory(equality)],[c_496,c_922])).

tff(c_293,plain,(
    ! [A_89,B_90] :
      ( r2_hidden('#skF_2'(A_89,B_90),B_90)
      | r1_xboole_0(A_89,B_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_18,plain,(
    ! [A_13,B_14,C_17] :
      ( ~ r1_xboole_0(A_13,B_14)
      | ~ r2_hidden(C_17,k3_xboole_0(A_13,B_14)) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_298,plain,(
    ! [A_13,B_14,A_89] :
      ( ~ r1_xboole_0(A_13,B_14)
      | r1_xboole_0(A_89,k3_xboole_0(A_13,B_14)) ) ),
    inference(resolution,[status(thm)],[c_293,c_18])).

tff(c_1166,plain,(
    ! [A_166,A_89] :
      ( ~ r1_xboole_0(A_166,k1_xboole_0)
      | r1_xboole_0(A_89,k3_subset_1(A_166,A_166)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1142,c_298])).

tff(c_1202,plain,(
    ! [A_89,A_166] : r1_xboole_0(A_89,k3_subset_1(A_166,A_166)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_1166])).

tff(c_1246,plain,(
    ! [C_171,B_172,D_173,A_174] :
      ( C_171 = B_172
      | ~ r1_xboole_0(D_173,B_172)
      | ~ r1_xboole_0(C_171,A_174)
      | k2_xboole_0(C_171,D_173) != k2_xboole_0(A_174,B_172) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_1258,plain,(
    ! [C_171,A_174,A_21] :
      ( k1_xboole_0 = C_171
      | ~ r1_xboole_0(C_171,A_174)
      | k2_xboole_0(C_171,A_21) != k2_xboole_0(A_174,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_24,c_1246])).

tff(c_2188,plain,(
    ! [C_224,A_225,A_226] :
      ( k1_xboole_0 = C_224
      | ~ r1_xboole_0(C_224,A_225)
      | k2_xboole_0(C_224,A_226) != A_225 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_1258])).

tff(c_2707,plain,(
    ! [A_252,A_253,A_254] :
      ( k1_xboole_0 = A_252
      | k3_subset_1(A_253,A_253) != k2_xboole_0(A_252,A_254) ) ),
    inference(resolution,[status(thm)],[c_1202,c_2188])).

tff(c_2817,plain,(
    ! [A_253] : k3_subset_1(A_253,A_253) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_2707])).

tff(c_74,plain,(
    ! [A_49,B_50] :
      ( k3_subset_1(A_49,k3_subset_1(A_49,B_50)) = B_50
      | ~ m1_subset_1(B_50,k1_zfmisc_1(A_49)) ) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_920,plain,(
    ! [A_156] : k3_subset_1(A_156,k3_subset_1(A_156,A_156)) = A_156 ),
    inference(resolution,[status(thm)],[c_910,c_74])).

tff(c_2828,plain,(
    ! [A_156] : k3_subset_1(A_156,k1_xboole_0) = A_156 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2817,c_920])).

tff(c_66,plain,(
    ! [A_44] : k1_subset_1(A_44) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_68,plain,(
    ! [A_45] : k2_subset_1(A_45) = A_45 ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_76,plain,(
    k3_subset_1('#skF_4',k1_subset_1('#skF_4')) != k2_subset_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_77,plain,(
    k3_subset_1('#skF_4',k1_subset_1('#skF_4')) != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_76])).

tff(c_78,plain,(
    k3_subset_1('#skF_4',k1_xboole_0) != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_77])).

tff(c_3175,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2828,c_78])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.07  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.07  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.07/0.26  % Computer   : n023.cluster.edu
% 0.07/0.26  % Model      : x86_64 x86_64
% 0.07/0.26  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.07/0.26  % Memory     : 8042.1875MB
% 0.07/0.26  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.07/0.26  % CPULimit   : 60
% 0.07/0.26  % DateTime   : Tue Dec  1 14:58:05 EST 2020
% 0.07/0.26  % CPUTime    : 
% 0.07/0.26  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.16/1.69  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.37/1.70  
% 4.37/1.70  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.37/1.70  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k2_subset_1 > k1_zfmisc_1 > k1_tarski > k1_subset_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 4.37/1.70  
% 4.37/1.70  %Foreground sorts:
% 4.37/1.70  
% 4.37/1.70  
% 4.37/1.70  %Background operators:
% 4.37/1.70  
% 4.37/1.70  
% 4.37/1.70  %Foreground operators:
% 4.37/1.70  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.37/1.70  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.37/1.70  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.37/1.70  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.37/1.70  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.37/1.70  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 4.37/1.70  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.37/1.70  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.37/1.70  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 4.37/1.70  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.37/1.70  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.37/1.70  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.37/1.70  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.37/1.70  tff('#skF_4', type, '#skF_4': $i).
% 4.37/1.70  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.37/1.70  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.37/1.70  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 4.37/1.70  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.37/1.70  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.37/1.70  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.37/1.70  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 4.37/1.70  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.37/1.70  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.37/1.70  
% 4.37/1.71  tff(f_68, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 4.37/1.71  tff(f_72, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 4.37/1.71  tff(f_84, axiom, (![A, B]: (r1_xboole_0(A, B) => (k4_xboole_0(k2_xboole_0(A, B), B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_xboole_1)).
% 4.37/1.71  tff(f_70, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 4.37/1.71  tff(f_147, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 4.37/1.71  tff(f_123, axiom, (![A]: r1_tarski(k1_tarski(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t80_zfmisc_1)).
% 4.37/1.71  tff(f_86, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 4.37/1.71  tff(f_121, axiom, (![A, B, C]: ((k4_xboole_0(A, k2_tarski(B, C)) = k1_xboole_0) <=> ~(((~(A = k1_xboole_0) & ~(A = k1_tarski(B))) & ~(A = k1_tarski(C))) & ~(A = k2_tarski(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t75_zfmisc_1)).
% 4.37/1.71  tff(f_106, axiom, (![A, B, C]: ((k4_xboole_0(k2_tarski(A, B), C) = k1_xboole_0) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_zfmisc_1)).
% 4.37/1.71  tff(f_34, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 4.37/1.71  tff(f_136, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 4.37/1.71  tff(f_144, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 4.37/1.71  tff(f_52, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 4.37/1.71  tff(f_66, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 4.37/1.71  tff(f_80, axiom, (![A, B, C, D]: ((((k2_xboole_0(A, B) = k2_xboole_0(C, D)) & r1_xboole_0(C, A)) & r1_xboole_0(D, B)) => (C = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_xboole_1)).
% 4.37/1.71  tff(f_151, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 4.37/1.71  tff(f_138, axiom, (![A]: (k1_subset_1(A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_subset_1)).
% 4.37/1.71  tff(f_140, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 4.37/1.71  tff(f_154, negated_conjecture, ~(![A]: (k2_subset_1(A) = k3_subset_1(A, k1_subset_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_subset_1)).
% 4.37/1.71  tff(c_20, plain, (![A_18]: (k2_xboole_0(A_18, k1_xboole_0)=A_18)), inference(cnfTransformation, [status(thm)], [f_68])).
% 4.37/1.71  tff(c_24, plain, (![A_21]: (r1_xboole_0(A_21, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.37/1.71  tff(c_461, plain, (![A_115, B_116]: (k4_xboole_0(k2_xboole_0(A_115, B_116), B_116)=A_115 | ~r1_xboole_0(A_115, B_116))), inference(cnfTransformation, [status(thm)], [f_84])).
% 4.37/1.71  tff(c_473, plain, (![A_18]: (k4_xboole_0(A_18, k1_xboole_0)=A_18 | ~r1_xboole_0(A_18, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_20, c_461])).
% 4.37/1.71  tff(c_486, plain, (![A_117]: (k4_xboole_0(A_117, k1_xboole_0)=A_117)), inference(demodulation, [status(thm), theory('equality')], [c_24, c_473])).
% 4.37/1.71  tff(c_22, plain, (![A_19, B_20]: (k4_xboole_0(A_19, k4_xboole_0(A_19, B_20))=k3_xboole_0(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_70])).
% 4.37/1.71  tff(c_496, plain, (![A_117]: (k4_xboole_0(A_117, A_117)=k3_xboole_0(A_117, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_486, c_22])).
% 4.37/1.71  tff(c_72, plain, (![A_48]: (~v1_xboole_0(k1_zfmisc_1(A_48)))), inference(cnfTransformation, [status(thm)], [f_147])).
% 4.37/1.71  tff(c_56, plain, (![A_41]: (r1_tarski(k1_tarski(A_41), k1_zfmisc_1(A_41)))), inference(cnfTransformation, [status(thm)], [f_123])).
% 4.37/1.71  tff(c_30, plain, (![A_28]: (k2_tarski(A_28, A_28)=k1_tarski(A_28))), inference(cnfTransformation, [status(thm)], [f_86])).
% 4.37/1.71  tff(c_48, plain, (![B_39, C_40]: (k4_xboole_0(k2_tarski(B_39, C_40), k2_tarski(B_39, C_40))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_121])).
% 4.37/1.71  tff(c_535, plain, (![B_121, C_122, A_123]: (r2_hidden(B_121, C_122) | k4_xboole_0(k2_tarski(A_123, B_121), C_122)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_106])).
% 4.37/1.71  tff(c_556, plain, (![C_126, B_127]: (r2_hidden(C_126, k2_tarski(B_127, C_126)))), inference(superposition, [status(thm), theory('equality')], [c_48, c_535])).
% 4.37/1.71  tff(c_580, plain, (![A_131]: (r2_hidden(A_131, k1_tarski(A_131)))), inference(superposition, [status(thm), theory('equality')], [c_30, c_556])).
% 4.37/1.71  tff(c_4, plain, (![C_7, B_4, A_3]: (r2_hidden(C_7, B_4) | ~r2_hidden(C_7, A_3) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 4.37/1.71  tff(c_889, plain, (![A_153, B_154]: (r2_hidden(A_153, B_154) | ~r1_tarski(k1_tarski(A_153), B_154))), inference(resolution, [status(thm)], [c_580, c_4])).
% 4.37/1.71  tff(c_900, plain, (![A_155]: (r2_hidden(A_155, k1_zfmisc_1(A_155)))), inference(resolution, [status(thm)], [c_56, c_889])).
% 4.37/1.71  tff(c_58, plain, (![B_43, A_42]: (m1_subset_1(B_43, A_42) | ~r2_hidden(B_43, A_42) | v1_xboole_0(A_42))), inference(cnfTransformation, [status(thm)], [f_136])).
% 4.37/1.71  tff(c_905, plain, (![A_155]: (m1_subset_1(A_155, k1_zfmisc_1(A_155)) | v1_xboole_0(k1_zfmisc_1(A_155)))), inference(resolution, [status(thm)], [c_900, c_58])).
% 4.37/1.71  tff(c_910, plain, (![A_156]: (m1_subset_1(A_156, k1_zfmisc_1(A_156)))), inference(negUnitSimplification, [status(thm)], [c_72, c_905])).
% 4.37/1.71  tff(c_70, plain, (![A_46, B_47]: (k4_xboole_0(A_46, B_47)=k3_subset_1(A_46, B_47) | ~m1_subset_1(B_47, k1_zfmisc_1(A_46)))), inference(cnfTransformation, [status(thm)], [f_144])).
% 4.37/1.71  tff(c_922, plain, (![A_157]: (k4_xboole_0(A_157, A_157)=k3_subset_1(A_157, A_157))), inference(resolution, [status(thm)], [c_910, c_70])).
% 4.37/1.71  tff(c_1142, plain, (![A_166]: (k3_xboole_0(A_166, k1_xboole_0)=k3_subset_1(A_166, A_166))), inference(superposition, [status(thm), theory('equality')], [c_496, c_922])).
% 4.37/1.71  tff(c_293, plain, (![A_89, B_90]: (r2_hidden('#skF_2'(A_89, B_90), B_90) | r1_xboole_0(A_89, B_90))), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.37/1.71  tff(c_18, plain, (![A_13, B_14, C_17]: (~r1_xboole_0(A_13, B_14) | ~r2_hidden(C_17, k3_xboole_0(A_13, B_14)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 4.37/1.71  tff(c_298, plain, (![A_13, B_14, A_89]: (~r1_xboole_0(A_13, B_14) | r1_xboole_0(A_89, k3_xboole_0(A_13, B_14)))), inference(resolution, [status(thm)], [c_293, c_18])).
% 4.37/1.71  tff(c_1166, plain, (![A_166, A_89]: (~r1_xboole_0(A_166, k1_xboole_0) | r1_xboole_0(A_89, k3_subset_1(A_166, A_166)))), inference(superposition, [status(thm), theory('equality')], [c_1142, c_298])).
% 4.37/1.71  tff(c_1202, plain, (![A_89, A_166]: (r1_xboole_0(A_89, k3_subset_1(A_166, A_166)))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_1166])).
% 4.37/1.71  tff(c_1246, plain, (![C_171, B_172, D_173, A_174]: (C_171=B_172 | ~r1_xboole_0(D_173, B_172) | ~r1_xboole_0(C_171, A_174) | k2_xboole_0(C_171, D_173)!=k2_xboole_0(A_174, B_172))), inference(cnfTransformation, [status(thm)], [f_80])).
% 4.37/1.71  tff(c_1258, plain, (![C_171, A_174, A_21]: (k1_xboole_0=C_171 | ~r1_xboole_0(C_171, A_174) | k2_xboole_0(C_171, A_21)!=k2_xboole_0(A_174, k1_xboole_0))), inference(resolution, [status(thm)], [c_24, c_1246])).
% 4.37/1.71  tff(c_2188, plain, (![C_224, A_225, A_226]: (k1_xboole_0=C_224 | ~r1_xboole_0(C_224, A_225) | k2_xboole_0(C_224, A_226)!=A_225)), inference(demodulation, [status(thm), theory('equality')], [c_20, c_1258])).
% 4.37/1.71  tff(c_2707, plain, (![A_252, A_253, A_254]: (k1_xboole_0=A_252 | k3_subset_1(A_253, A_253)!=k2_xboole_0(A_252, A_254))), inference(resolution, [status(thm)], [c_1202, c_2188])).
% 4.37/1.71  tff(c_2817, plain, (![A_253]: (k3_subset_1(A_253, A_253)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_20, c_2707])).
% 4.37/1.71  tff(c_74, plain, (![A_49, B_50]: (k3_subset_1(A_49, k3_subset_1(A_49, B_50))=B_50 | ~m1_subset_1(B_50, k1_zfmisc_1(A_49)))), inference(cnfTransformation, [status(thm)], [f_151])).
% 4.37/1.71  tff(c_920, plain, (![A_156]: (k3_subset_1(A_156, k3_subset_1(A_156, A_156))=A_156)), inference(resolution, [status(thm)], [c_910, c_74])).
% 4.37/1.71  tff(c_2828, plain, (![A_156]: (k3_subset_1(A_156, k1_xboole_0)=A_156)), inference(demodulation, [status(thm), theory('equality')], [c_2817, c_920])).
% 4.37/1.71  tff(c_66, plain, (![A_44]: (k1_subset_1(A_44)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_138])).
% 4.37/1.71  tff(c_68, plain, (![A_45]: (k2_subset_1(A_45)=A_45)), inference(cnfTransformation, [status(thm)], [f_140])).
% 4.37/1.71  tff(c_76, plain, (k3_subset_1('#skF_4', k1_subset_1('#skF_4'))!=k2_subset_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_154])).
% 4.37/1.71  tff(c_77, plain, (k3_subset_1('#skF_4', k1_subset_1('#skF_4'))!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_76])).
% 4.37/1.71  tff(c_78, plain, (k3_subset_1('#skF_4', k1_xboole_0)!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_77])).
% 4.37/1.71  tff(c_3175, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2828, c_78])).
% 4.37/1.71  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.37/1.71  
% 4.37/1.71  Inference rules
% 4.37/1.71  ----------------------
% 4.37/1.71  #Ref     : 3
% 4.37/1.71  #Sup     : 720
% 4.37/1.71  #Fact    : 0
% 4.37/1.71  #Define  : 0
% 4.37/1.71  #Split   : 2
% 4.37/1.71  #Chain   : 0
% 4.37/1.71  #Close   : 0
% 4.37/1.71  
% 4.37/1.71  Ordering : KBO
% 4.37/1.71  
% 4.37/1.71  Simplification rules
% 4.37/1.71  ----------------------
% 4.37/1.71  #Subsume      : 132
% 4.37/1.71  #Demod        : 550
% 4.37/1.71  #Tautology    : 425
% 4.37/1.71  #SimpNegUnit  : 52
% 4.37/1.71  #BackRed      : 32
% 4.37/1.71  
% 4.37/1.71  #Partial instantiations: 0
% 4.37/1.71  #Strategies tried      : 1
% 4.37/1.71  
% 4.37/1.71  Timing (in seconds)
% 4.37/1.71  ----------------------
% 4.37/1.72  Preprocessing        : 0.40
% 4.37/1.72  Parsing              : 0.19
% 4.37/1.72  CNF conversion       : 0.03
% 4.37/1.72  Main loop            : 0.66
% 4.37/1.72  Inferencing          : 0.22
% 4.37/1.72  Reduction            : 0.26
% 4.37/1.72  Demodulation         : 0.19
% 4.37/1.72  BG Simplification    : 0.03
% 4.37/1.72  Subsumption          : 0.10
% 4.37/1.72  Abstraction          : 0.03
% 4.37/1.72  MUC search           : 0.00
% 4.37/1.72  Cooper               : 0.00
% 4.37/1.72  Total                : 1.09
% 4.37/1.72  Index Insertion      : 0.00
% 4.37/1.72  Index Deletion       : 0.00
% 4.37/1.72  Index Matching       : 0.00
% 4.37/1.72  BG Taut test         : 0.00
%------------------------------------------------------------------------------
