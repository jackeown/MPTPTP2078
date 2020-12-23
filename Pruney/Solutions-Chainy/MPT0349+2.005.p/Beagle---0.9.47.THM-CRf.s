%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:24 EST 2020

% Result     : Theorem 3.20s
% Output     : CNFRefutation 3.20s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 120 expanded)
%              Number of leaves         :   37 (  55 expanded)
%              Depth                    :   14
%              Number of atoms          :   72 ( 147 expanded)
%              Number of equality atoms :   32 (  59 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tarski > #nlpp > k2_subset_1 > k1_zfmisc_1 > k1_tarski > k1_subset_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff(f_74,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_70,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_88,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => k4_xboole_0(k2_xboole_0(A,B),B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_xboole_1)).

tff(f_72,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_132,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_108,axiom,(
    ! [A] : r1_tarski(k1_tarski(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_zfmisc_1)).

tff(f_106,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),B) = k1_xboole_0
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t68_zfmisc_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_121,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_129,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_136,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_123,axiom,(
    ! [A] : k1_subset_1(A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).

tff(f_125,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_139,negated_conjecture,(
    ~ ! [A] : k2_subset_1(A) = k3_subset_1(A,k1_subset_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_subset_1)).

tff(c_26,plain,(
    ! [A_21] : r1_xboole_0(A_21,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_118,plain,(
    ! [A_67,B_68] :
      ( k3_xboole_0(A_67,B_68) = k1_xboole_0
      | ~ r1_xboole_0(A_67,B_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_134,plain,(
    ! [A_21] : k3_xboole_0(A_21,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_26,c_118])).

tff(c_22,plain,(
    ! [A_18] : k2_xboole_0(A_18,k1_xboole_0) = A_18 ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_602,plain,(
    ! [A_126,B_127] :
      ( k4_xboole_0(k2_xboole_0(A_126,B_127),B_127) = A_126
      | ~ r1_xboole_0(A_126,B_127) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_629,plain,(
    ! [A_18] :
      ( k4_xboole_0(A_18,k1_xboole_0) = A_18
      | ~ r1_xboole_0(A_18,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_602])).

tff(c_634,plain,(
    ! [A_128] : k4_xboole_0(A_128,k1_xboole_0) = A_128 ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_629])).

tff(c_24,plain,(
    ! [A_19,B_20] : k4_xboole_0(A_19,k4_xboole_0(A_19,B_20)) = k3_xboole_0(A_19,B_20) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_650,plain,(
    ! [A_128] : k4_xboole_0(A_128,A_128) = k3_xboole_0(A_128,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_634,c_24])).

tff(c_681,plain,(
    ! [A_128] : k4_xboole_0(A_128,A_128) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_134,c_650])).

tff(c_64,plain,(
    ! [A_46] : ~ v1_xboole_0(k1_zfmisc_1(A_46)) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_48,plain,(
    ! [A_39] : r1_tarski(k1_tarski(A_39),k1_zfmisc_1(A_39)) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_715,plain,(
    ! [A_133] : k4_xboole_0(A_133,A_133) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_134,c_650])).

tff(c_44,plain,(
    ! [A_37,B_38] :
      ( r2_hidden(A_37,B_38)
      | k4_xboole_0(k1_tarski(A_37),B_38) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_845,plain,(
    ! [A_137] : r2_hidden(A_137,k1_tarski(A_137)) ),
    inference(superposition,[status(thm),theory(equality)],[c_715,c_44])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1214,plain,(
    ! [A_162,B_163] :
      ( r2_hidden(A_162,B_163)
      | ~ r1_tarski(k1_tarski(A_162),B_163) ) ),
    inference(resolution,[status(thm)],[c_845,c_2])).

tff(c_1230,plain,(
    ! [A_164] : r2_hidden(A_164,k1_zfmisc_1(A_164)) ),
    inference(resolution,[status(thm)],[c_48,c_1214])).

tff(c_50,plain,(
    ! [B_41,A_40] :
      ( m1_subset_1(B_41,A_40)
      | ~ r2_hidden(B_41,A_40)
      | v1_xboole_0(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_1238,plain,(
    ! [A_164] :
      ( m1_subset_1(A_164,k1_zfmisc_1(A_164))
      | v1_xboole_0(k1_zfmisc_1(A_164)) ) ),
    inference(resolution,[status(thm)],[c_1230,c_50])).

tff(c_1270,plain,(
    ! [A_170] : m1_subset_1(A_170,k1_zfmisc_1(A_170)) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_1238])).

tff(c_62,plain,(
    ! [A_44,B_45] :
      ( k4_xboole_0(A_44,B_45) = k3_subset_1(A_44,B_45)
      | ~ m1_subset_1(B_45,k1_zfmisc_1(A_44)) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_1273,plain,(
    ! [A_170] : k4_xboole_0(A_170,A_170) = k3_subset_1(A_170,A_170) ),
    inference(resolution,[status(thm)],[c_1270,c_62])).

tff(c_1280,plain,(
    ! [A_170] : k3_subset_1(A_170,A_170) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_681,c_1273])).

tff(c_66,plain,(
    ! [A_47,B_48] :
      ( k3_subset_1(A_47,k3_subset_1(A_47,B_48)) = B_48
      | ~ m1_subset_1(B_48,k1_zfmisc_1(A_47)) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_1281,plain,(
    ! [A_170] : k3_subset_1(A_170,k3_subset_1(A_170,A_170)) = A_170 ),
    inference(resolution,[status(thm)],[c_1270,c_66])).

tff(c_1290,plain,(
    ! [A_170] : k3_subset_1(A_170,k1_xboole_0) = A_170 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1280,c_1281])).

tff(c_58,plain,(
    ! [A_42] : k1_subset_1(A_42) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_60,plain,(
    ! [A_43] : k2_subset_1(A_43) = A_43 ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_68,plain,(
    k3_subset_1('#skF_4',k1_subset_1('#skF_4')) != k2_subset_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_69,plain,(
    k3_subset_1('#skF_4',k1_subset_1('#skF_4')) != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_68])).

tff(c_70,plain,(
    k3_subset_1('#skF_4',k1_xboole_0) != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_69])).

tff(c_1293,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1290,c_70])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:56:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.20/1.62  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.20/1.63  
% 3.20/1.63  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.20/1.63  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tarski > #nlpp > k2_subset_1 > k1_zfmisc_1 > k1_tarski > k1_subset_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 3.20/1.63  
% 3.20/1.63  %Foreground sorts:
% 3.20/1.63  
% 3.20/1.63  
% 3.20/1.63  %Background operators:
% 3.20/1.63  
% 3.20/1.63  
% 3.20/1.63  %Foreground operators:
% 3.20/1.63  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.20/1.63  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.20/1.63  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.20/1.63  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.20/1.63  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.20/1.63  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.20/1.63  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.20/1.63  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.20/1.63  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 3.20/1.63  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.20/1.63  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.20/1.63  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.20/1.63  tff('#skF_4', type, '#skF_4': $i).
% 3.20/1.63  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.20/1.63  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.20/1.63  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 3.20/1.63  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.20/1.63  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.20/1.63  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.20/1.63  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 3.20/1.63  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.20/1.63  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.20/1.63  
% 3.20/1.64  tff(f_74, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 3.20/1.64  tff(f_36, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 3.20/1.64  tff(f_70, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 3.20/1.64  tff(f_88, axiom, (![A, B]: (r1_xboole_0(A, B) => (k4_xboole_0(k2_xboole_0(A, B), B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_xboole_1)).
% 3.20/1.64  tff(f_72, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 3.20/1.64  tff(f_132, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 3.20/1.64  tff(f_108, axiom, (![A]: r1_tarski(k1_tarski(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t80_zfmisc_1)).
% 3.20/1.64  tff(f_106, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_xboole_0) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t68_zfmisc_1)).
% 3.20/1.64  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 3.20/1.64  tff(f_121, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 3.20/1.64  tff(f_129, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 3.20/1.64  tff(f_136, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 3.20/1.64  tff(f_123, axiom, (![A]: (k1_subset_1(A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_subset_1)).
% 3.20/1.64  tff(f_125, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 3.20/1.64  tff(f_139, negated_conjecture, ~(![A]: (k2_subset_1(A) = k3_subset_1(A, k1_subset_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_subset_1)).
% 3.20/1.64  tff(c_26, plain, (![A_21]: (r1_xboole_0(A_21, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.20/1.64  tff(c_118, plain, (![A_67, B_68]: (k3_xboole_0(A_67, B_68)=k1_xboole_0 | ~r1_xboole_0(A_67, B_68))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.20/1.64  tff(c_134, plain, (![A_21]: (k3_xboole_0(A_21, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_26, c_118])).
% 3.20/1.64  tff(c_22, plain, (![A_18]: (k2_xboole_0(A_18, k1_xboole_0)=A_18)), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.20/1.64  tff(c_602, plain, (![A_126, B_127]: (k4_xboole_0(k2_xboole_0(A_126, B_127), B_127)=A_126 | ~r1_xboole_0(A_126, B_127))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.20/1.64  tff(c_629, plain, (![A_18]: (k4_xboole_0(A_18, k1_xboole_0)=A_18 | ~r1_xboole_0(A_18, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_22, c_602])).
% 3.20/1.64  tff(c_634, plain, (![A_128]: (k4_xboole_0(A_128, k1_xboole_0)=A_128)), inference(demodulation, [status(thm), theory('equality')], [c_26, c_629])).
% 3.20/1.64  tff(c_24, plain, (![A_19, B_20]: (k4_xboole_0(A_19, k4_xboole_0(A_19, B_20))=k3_xboole_0(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.20/1.64  tff(c_650, plain, (![A_128]: (k4_xboole_0(A_128, A_128)=k3_xboole_0(A_128, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_634, c_24])).
% 3.20/1.64  tff(c_681, plain, (![A_128]: (k4_xboole_0(A_128, A_128)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_134, c_650])).
% 3.20/1.64  tff(c_64, plain, (![A_46]: (~v1_xboole_0(k1_zfmisc_1(A_46)))), inference(cnfTransformation, [status(thm)], [f_132])).
% 3.20/1.64  tff(c_48, plain, (![A_39]: (r1_tarski(k1_tarski(A_39), k1_zfmisc_1(A_39)))), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.20/1.64  tff(c_715, plain, (![A_133]: (k4_xboole_0(A_133, A_133)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_134, c_650])).
% 3.20/1.64  tff(c_44, plain, (![A_37, B_38]: (r2_hidden(A_37, B_38) | k4_xboole_0(k1_tarski(A_37), B_38)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.20/1.64  tff(c_845, plain, (![A_137]: (r2_hidden(A_137, k1_tarski(A_137)))), inference(superposition, [status(thm), theory('equality')], [c_715, c_44])).
% 3.20/1.64  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.20/1.64  tff(c_1214, plain, (![A_162, B_163]: (r2_hidden(A_162, B_163) | ~r1_tarski(k1_tarski(A_162), B_163))), inference(resolution, [status(thm)], [c_845, c_2])).
% 3.20/1.64  tff(c_1230, plain, (![A_164]: (r2_hidden(A_164, k1_zfmisc_1(A_164)))), inference(resolution, [status(thm)], [c_48, c_1214])).
% 3.20/1.64  tff(c_50, plain, (![B_41, A_40]: (m1_subset_1(B_41, A_40) | ~r2_hidden(B_41, A_40) | v1_xboole_0(A_40))), inference(cnfTransformation, [status(thm)], [f_121])).
% 3.20/1.64  tff(c_1238, plain, (![A_164]: (m1_subset_1(A_164, k1_zfmisc_1(A_164)) | v1_xboole_0(k1_zfmisc_1(A_164)))), inference(resolution, [status(thm)], [c_1230, c_50])).
% 3.20/1.64  tff(c_1270, plain, (![A_170]: (m1_subset_1(A_170, k1_zfmisc_1(A_170)))), inference(negUnitSimplification, [status(thm)], [c_64, c_1238])).
% 3.20/1.64  tff(c_62, plain, (![A_44, B_45]: (k4_xboole_0(A_44, B_45)=k3_subset_1(A_44, B_45) | ~m1_subset_1(B_45, k1_zfmisc_1(A_44)))), inference(cnfTransformation, [status(thm)], [f_129])).
% 3.20/1.64  tff(c_1273, plain, (![A_170]: (k4_xboole_0(A_170, A_170)=k3_subset_1(A_170, A_170))), inference(resolution, [status(thm)], [c_1270, c_62])).
% 3.20/1.64  tff(c_1280, plain, (![A_170]: (k3_subset_1(A_170, A_170)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_681, c_1273])).
% 3.20/1.64  tff(c_66, plain, (![A_47, B_48]: (k3_subset_1(A_47, k3_subset_1(A_47, B_48))=B_48 | ~m1_subset_1(B_48, k1_zfmisc_1(A_47)))), inference(cnfTransformation, [status(thm)], [f_136])).
% 3.20/1.64  tff(c_1281, plain, (![A_170]: (k3_subset_1(A_170, k3_subset_1(A_170, A_170))=A_170)), inference(resolution, [status(thm)], [c_1270, c_66])).
% 3.20/1.64  tff(c_1290, plain, (![A_170]: (k3_subset_1(A_170, k1_xboole_0)=A_170)), inference(demodulation, [status(thm), theory('equality')], [c_1280, c_1281])).
% 3.20/1.64  tff(c_58, plain, (![A_42]: (k1_subset_1(A_42)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_123])).
% 3.20/1.64  tff(c_60, plain, (![A_43]: (k2_subset_1(A_43)=A_43)), inference(cnfTransformation, [status(thm)], [f_125])).
% 3.20/1.64  tff(c_68, plain, (k3_subset_1('#skF_4', k1_subset_1('#skF_4'))!=k2_subset_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_139])).
% 3.20/1.64  tff(c_69, plain, (k3_subset_1('#skF_4', k1_subset_1('#skF_4'))!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_60, c_68])).
% 3.20/1.64  tff(c_70, plain, (k3_subset_1('#skF_4', k1_xboole_0)!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_58, c_69])).
% 3.20/1.64  tff(c_1293, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1290, c_70])).
% 3.20/1.64  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.20/1.64  
% 3.20/1.64  Inference rules
% 3.20/1.64  ----------------------
% 3.20/1.64  #Ref     : 0
% 3.20/1.64  #Sup     : 282
% 3.20/1.64  #Fact    : 0
% 3.20/1.64  #Define  : 0
% 3.20/1.64  #Split   : 2
% 3.20/1.64  #Chain   : 0
% 3.20/1.64  #Close   : 0
% 3.20/1.64  
% 3.20/1.64  Ordering : KBO
% 3.20/1.64  
% 3.20/1.64  Simplification rules
% 3.20/1.64  ----------------------
% 3.20/1.64  #Subsume      : 53
% 3.20/1.64  #Demod        : 102
% 3.20/1.64  #Tautology    : 150
% 3.20/1.64  #SimpNegUnit  : 13
% 3.20/1.64  #BackRed      : 2
% 3.20/1.64  
% 3.20/1.64  #Partial instantiations: 0
% 3.20/1.64  #Strategies tried      : 1
% 3.20/1.64  
% 3.20/1.64  Timing (in seconds)
% 3.20/1.64  ----------------------
% 3.20/1.64  Preprocessing        : 0.46
% 3.20/1.64  Parsing              : 0.30
% 3.20/1.64  CNF conversion       : 0.02
% 3.20/1.64  Main loop            : 0.36
% 3.20/1.64  Inferencing          : 0.13
% 3.20/1.64  Reduction            : 0.11
% 3.20/1.64  Demodulation         : 0.08
% 3.20/1.64  BG Simplification    : 0.02
% 3.20/1.64  Subsumption          : 0.06
% 3.20/1.64  Abstraction          : 0.02
% 3.20/1.64  MUC search           : 0.00
% 3.20/1.64  Cooper               : 0.00
% 3.20/1.64  Total                : 0.85
% 3.20/1.64  Index Insertion      : 0.00
% 3.20/1.65  Index Deletion       : 0.00
% 3.20/1.65  Index Matching       : 0.00
% 3.20/1.65  BG Taut test         : 0.00
%------------------------------------------------------------------------------
