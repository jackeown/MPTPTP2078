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
% DateTime   : Thu Dec  3 10:02:40 EST 2020

% Result     : Theorem 4.21s
% Output     : CNFRefutation 4.47s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 194 expanded)
%              Number of leaves         :   32 (  79 expanded)
%              Depth                    :   12
%              Number of atoms          :  101 ( 341 expanded)
%              Number of equality atoms :   27 (  63 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k7_relat_1 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k10_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_144,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => ( r1_xboole_0(k2_relat_1(A),k2_relat_1(B))
             => r1_xboole_0(A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t215_relat_1)).

tff(f_126,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k2_relat_1(k3_xboole_0(A,B)),k3_xboole_0(k2_relat_1(A),k2_relat_1(B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_relat_1)).

tff(f_47,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k4_xboole_0(B,C))
     => ( r1_tarski(A,B)
        & r1_xboole_0(A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).

tff(f_59,axiom,(
    ! [A] :
      ( ~ ( ~ r1_xboole_0(A,A)
          & A = k1_xboole_0 )
      & ~ ( A != k1_xboole_0
          & r1_xboole_0(A,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_xboole_1)).

tff(f_88,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_relat_1)).

tff(f_92,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k7_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t110_relat_1)).

tff(f_84,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_134,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

tff(c_135,plain,(
    ! [A_63,B_64] :
      ( r1_xboole_0(A_63,B_64)
      | k3_xboole_0(A_63,B_64) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_6,plain,(
    ! [B_4,A_3] :
      ( r1_xboole_0(B_4,A_3)
      | ~ r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_417,plain,(
    ! [B_84,A_85] :
      ( r1_xboole_0(B_84,A_85)
      | k3_xboole_0(A_85,B_84) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_135,c_6])).

tff(c_56,plain,(
    ~ r1_xboole_0('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_442,plain,(
    k3_xboole_0('#skF_4','#skF_3') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_417,c_56])).

tff(c_60,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_62,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_58,plain,(
    r1_xboole_0(k2_relat_1('#skF_3'),k2_relat_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_72,plain,(
    ! [B_55,A_56] :
      ( r1_xboole_0(B_55,A_56)
      | ~ r1_xboole_0(A_56,B_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_77,plain,(
    r1_xboole_0(k2_relat_1('#skF_4'),k2_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_58,c_72])).

tff(c_301,plain,(
    ! [A_78,B_79] :
      ( k3_xboole_0(A_78,B_79) = k1_xboole_0
      | ~ r1_xboole_0(A_78,B_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_322,plain,(
    k3_xboole_0(k2_relat_1('#skF_4'),k2_relat_1('#skF_3')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_77,c_301])).

tff(c_1872,plain,(
    ! [A_190,B_191] :
      ( r1_tarski(k2_relat_1(k3_xboole_0(A_190,B_191)),k3_xboole_0(k2_relat_1(A_190),k2_relat_1(B_191)))
      | ~ v1_relat_1(B_191)
      | ~ v1_relat_1(A_190) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_1886,plain,
    ( r1_tarski(k2_relat_1(k3_xboole_0('#skF_4','#skF_3')),k1_xboole_0)
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_322,c_1872])).

tff(c_1901,plain,(
    r1_tarski(k2_relat_1(k3_xboole_0('#skF_4','#skF_3')),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_62,c_1886])).

tff(c_14,plain,(
    ! [A_11] : r1_xboole_0(A_11,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_78,plain,(
    ! [A_11] : r1_xboole_0(k1_xboole_0,A_11) ),
    inference(resolution,[status(thm)],[c_14,c_72])).

tff(c_221,plain,(
    ! [A_71,B_72] :
      ( k4_xboole_0(A_71,B_72) = A_71
      | ~ r1_xboole_0(A_71,B_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_243,plain,(
    ! [A_11] : k4_xboole_0(k1_xboole_0,A_11) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_78,c_221])).

tff(c_443,plain,(
    ! [A_86,C_87,B_88] :
      ( r1_xboole_0(A_86,C_87)
      | ~ r1_tarski(A_86,k4_xboole_0(B_88,C_87)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_451,plain,(
    ! [A_89,A_90] :
      ( r1_xboole_0(A_89,A_90)
      | ~ r1_tarski(A_89,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_243,c_443])).

tff(c_18,plain,(
    ! [A_12] :
      ( ~ r1_xboole_0(A_12,A_12)
      | k1_xboole_0 = A_12 ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_475,plain,(
    ! [A_90] :
      ( k1_xboole_0 = A_90
      | ~ r1_tarski(A_90,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_451,c_18])).

tff(c_2020,plain,(
    k2_relat_1(k3_xboole_0('#skF_4','#skF_3')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1901,c_475])).

tff(c_36,plain,(
    ! [A_38,B_39] :
      ( v1_relat_1(k3_xboole_0(A_38,B_39))
      | ~ v1_relat_1(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_323,plain,(
    ! [A_11] : k3_xboole_0(k1_xboole_0,A_11) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_78,c_301])).

tff(c_95,plain,(
    ! [A_60] :
      ( k7_relat_1(A_60,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_107,plain,(
    k7_relat_1('#skF_3',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_62,c_95])).

tff(c_116,plain,(
    ! [A_61,B_62] :
      ( v1_relat_1(k7_relat_1(A_61,B_62))
      | ~ v1_relat_1(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_122,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_107,c_116])).

tff(c_128,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_122])).

tff(c_325,plain,(
    ! [A_11] : k3_xboole_0(A_11,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_14,c_301])).

tff(c_1892,plain,(
    ! [A_11] :
      ( r1_tarski(k2_relat_1(k1_xboole_0),k3_xboole_0(k2_relat_1(A_11),k2_relat_1(k1_xboole_0)))
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_11) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_325,c_1872])).

tff(c_2810,plain,(
    ! [A_232] :
      ( r1_tarski(k2_relat_1(k1_xboole_0),k3_xboole_0(k2_relat_1(A_232),k2_relat_1(k1_xboole_0)))
      | ~ v1_relat_1(A_232) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_128,c_1892])).

tff(c_2823,plain,
    ( r1_tarski(k2_relat_1(k1_xboole_0),k3_xboole_0(k1_xboole_0,k2_relat_1(k1_xboole_0)))
    | ~ v1_relat_1(k3_xboole_0('#skF_4','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2020,c_2810])).

tff(c_2832,plain,
    ( r1_tarski(k2_relat_1(k1_xboole_0),k1_xboole_0)
    | ~ v1_relat_1(k3_xboole_0('#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_323,c_2823])).

tff(c_2856,plain,(
    ~ v1_relat_1(k3_xboole_0('#skF_4','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_2832])).

tff(c_2859,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_2856])).

tff(c_2863,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_2859])).

tff(c_2865,plain,(
    v1_relat_1(k3_xboole_0('#skF_4','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_2832])).

tff(c_52,plain,(
    ! [A_51] :
      ( k2_relat_1(A_51) != k1_xboole_0
      | k1_xboole_0 = A_51
      | ~ v1_relat_1(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_2988,plain,
    ( k2_relat_1(k3_xboole_0('#skF_4','#skF_3')) != k1_xboole_0
    | k3_xboole_0('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2865,c_52])).

tff(c_2999,plain,(
    k3_xboole_0('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2020,c_2988])).

tff(c_3001,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_442,c_2999])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n006.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 15:10:22 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.21/1.72  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.21/1.73  
% 4.21/1.73  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.21/1.73  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k7_relat_1 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k10_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 4.21/1.73  
% 4.21/1.73  %Foreground sorts:
% 4.21/1.73  
% 4.21/1.73  
% 4.21/1.73  %Background operators:
% 4.21/1.73  
% 4.21/1.73  
% 4.21/1.73  %Foreground operators:
% 4.21/1.73  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.21/1.73  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.21/1.73  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.21/1.73  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.21/1.73  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 4.21/1.73  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 4.21/1.73  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.21/1.73  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.21/1.73  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.21/1.73  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.21/1.73  tff('#skF_3', type, '#skF_3': $i).
% 4.21/1.73  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.21/1.73  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 4.21/1.73  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.21/1.73  tff('#skF_4', type, '#skF_4': $i).
% 4.21/1.73  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.21/1.73  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.21/1.73  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.21/1.73  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.21/1.73  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.21/1.73  
% 4.47/1.74  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 4.47/1.74  tff(f_33, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 4.47/1.74  tff(f_144, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_xboole_0(k2_relat_1(A), k2_relat_1(B)) => r1_xboole_0(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t215_relat_1)).
% 4.47/1.74  tff(f_126, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k3_xboole_0(A, B)), k3_xboole_0(k2_relat_1(A), k2_relat_1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t27_relat_1)).
% 4.47/1.74  tff(f_47, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 4.47/1.74  tff(f_63, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 4.47/1.74  tff(f_39, axiom, (![A, B, C]: (r1_tarski(A, k4_xboole_0(B, C)) => (r1_tarski(A, B) & r1_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t106_xboole_1)).
% 4.47/1.74  tff(f_59, axiom, (![A]: (~(~r1_xboole_0(A, A) & (A = k1_xboole_0)) & ~(~(A = k1_xboole_0) & r1_xboole_0(A, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t66_xboole_1)).
% 4.47/1.74  tff(f_88, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_relat_1)).
% 4.47/1.74  tff(f_92, axiom, (![A]: (v1_relat_1(A) => (k7_relat_1(A, k1_xboole_0) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t110_relat_1)).
% 4.47/1.74  tff(f_84, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 4.47/1.74  tff(f_134, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_relat_1)).
% 4.47/1.74  tff(c_135, plain, (![A_63, B_64]: (r1_xboole_0(A_63, B_64) | k3_xboole_0(A_63, B_64)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.47/1.74  tff(c_6, plain, (![B_4, A_3]: (r1_xboole_0(B_4, A_3) | ~r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.47/1.74  tff(c_417, plain, (![B_84, A_85]: (r1_xboole_0(B_84, A_85) | k3_xboole_0(A_85, B_84)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_135, c_6])).
% 4.47/1.74  tff(c_56, plain, (~r1_xboole_0('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_144])).
% 4.47/1.74  tff(c_442, plain, (k3_xboole_0('#skF_4', '#skF_3')!=k1_xboole_0), inference(resolution, [status(thm)], [c_417, c_56])).
% 4.47/1.74  tff(c_60, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_144])).
% 4.47/1.74  tff(c_62, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_144])).
% 4.47/1.74  tff(c_58, plain, (r1_xboole_0(k2_relat_1('#skF_3'), k2_relat_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_144])).
% 4.47/1.74  tff(c_72, plain, (![B_55, A_56]: (r1_xboole_0(B_55, A_56) | ~r1_xboole_0(A_56, B_55))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.47/1.74  tff(c_77, plain, (r1_xboole_0(k2_relat_1('#skF_4'), k2_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_58, c_72])).
% 4.47/1.74  tff(c_301, plain, (![A_78, B_79]: (k3_xboole_0(A_78, B_79)=k1_xboole_0 | ~r1_xboole_0(A_78, B_79))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.47/1.74  tff(c_322, plain, (k3_xboole_0(k2_relat_1('#skF_4'), k2_relat_1('#skF_3'))=k1_xboole_0), inference(resolution, [status(thm)], [c_77, c_301])).
% 4.47/1.74  tff(c_1872, plain, (![A_190, B_191]: (r1_tarski(k2_relat_1(k3_xboole_0(A_190, B_191)), k3_xboole_0(k2_relat_1(A_190), k2_relat_1(B_191))) | ~v1_relat_1(B_191) | ~v1_relat_1(A_190))), inference(cnfTransformation, [status(thm)], [f_126])).
% 4.47/1.74  tff(c_1886, plain, (r1_tarski(k2_relat_1(k3_xboole_0('#skF_4', '#skF_3')), k1_xboole_0) | ~v1_relat_1('#skF_3') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_322, c_1872])).
% 4.47/1.74  tff(c_1901, plain, (r1_tarski(k2_relat_1(k3_xboole_0('#skF_4', '#skF_3')), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_60, c_62, c_1886])).
% 4.47/1.74  tff(c_14, plain, (![A_11]: (r1_xboole_0(A_11, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.47/1.74  tff(c_78, plain, (![A_11]: (r1_xboole_0(k1_xboole_0, A_11))), inference(resolution, [status(thm)], [c_14, c_72])).
% 4.47/1.74  tff(c_221, plain, (![A_71, B_72]: (k4_xboole_0(A_71, B_72)=A_71 | ~r1_xboole_0(A_71, B_72))), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.47/1.74  tff(c_243, plain, (![A_11]: (k4_xboole_0(k1_xboole_0, A_11)=k1_xboole_0)), inference(resolution, [status(thm)], [c_78, c_221])).
% 4.47/1.74  tff(c_443, plain, (![A_86, C_87, B_88]: (r1_xboole_0(A_86, C_87) | ~r1_tarski(A_86, k4_xboole_0(B_88, C_87)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.47/1.74  tff(c_451, plain, (![A_89, A_90]: (r1_xboole_0(A_89, A_90) | ~r1_tarski(A_89, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_243, c_443])).
% 4.47/1.74  tff(c_18, plain, (![A_12]: (~r1_xboole_0(A_12, A_12) | k1_xboole_0=A_12)), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.47/1.74  tff(c_475, plain, (![A_90]: (k1_xboole_0=A_90 | ~r1_tarski(A_90, k1_xboole_0))), inference(resolution, [status(thm)], [c_451, c_18])).
% 4.47/1.74  tff(c_2020, plain, (k2_relat_1(k3_xboole_0('#skF_4', '#skF_3'))=k1_xboole_0), inference(resolution, [status(thm)], [c_1901, c_475])).
% 4.47/1.74  tff(c_36, plain, (![A_38, B_39]: (v1_relat_1(k3_xboole_0(A_38, B_39)) | ~v1_relat_1(A_38))), inference(cnfTransformation, [status(thm)], [f_88])).
% 4.47/1.74  tff(c_323, plain, (![A_11]: (k3_xboole_0(k1_xboole_0, A_11)=k1_xboole_0)), inference(resolution, [status(thm)], [c_78, c_301])).
% 4.47/1.74  tff(c_95, plain, (![A_60]: (k7_relat_1(A_60, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_60))), inference(cnfTransformation, [status(thm)], [f_92])).
% 4.47/1.74  tff(c_107, plain, (k7_relat_1('#skF_3', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_62, c_95])).
% 4.47/1.74  tff(c_116, plain, (![A_61, B_62]: (v1_relat_1(k7_relat_1(A_61, B_62)) | ~v1_relat_1(A_61))), inference(cnfTransformation, [status(thm)], [f_84])).
% 4.47/1.74  tff(c_122, plain, (v1_relat_1(k1_xboole_0) | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_107, c_116])).
% 4.47/1.74  tff(c_128, plain, (v1_relat_1(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_62, c_122])).
% 4.47/1.74  tff(c_325, plain, (![A_11]: (k3_xboole_0(A_11, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_14, c_301])).
% 4.47/1.74  tff(c_1892, plain, (![A_11]: (r1_tarski(k2_relat_1(k1_xboole_0), k3_xboole_0(k2_relat_1(A_11), k2_relat_1(k1_xboole_0))) | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_11))), inference(superposition, [status(thm), theory('equality')], [c_325, c_1872])).
% 4.47/1.74  tff(c_2810, plain, (![A_232]: (r1_tarski(k2_relat_1(k1_xboole_0), k3_xboole_0(k2_relat_1(A_232), k2_relat_1(k1_xboole_0))) | ~v1_relat_1(A_232))), inference(demodulation, [status(thm), theory('equality')], [c_128, c_1892])).
% 4.47/1.74  tff(c_2823, plain, (r1_tarski(k2_relat_1(k1_xboole_0), k3_xboole_0(k1_xboole_0, k2_relat_1(k1_xboole_0))) | ~v1_relat_1(k3_xboole_0('#skF_4', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_2020, c_2810])).
% 4.47/1.74  tff(c_2832, plain, (r1_tarski(k2_relat_1(k1_xboole_0), k1_xboole_0) | ~v1_relat_1(k3_xboole_0('#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_323, c_2823])).
% 4.47/1.74  tff(c_2856, plain, (~v1_relat_1(k3_xboole_0('#skF_4', '#skF_3'))), inference(splitLeft, [status(thm)], [c_2832])).
% 4.47/1.74  tff(c_2859, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_36, c_2856])).
% 4.47/1.74  tff(c_2863, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_60, c_2859])).
% 4.47/1.74  tff(c_2865, plain, (v1_relat_1(k3_xboole_0('#skF_4', '#skF_3'))), inference(splitRight, [status(thm)], [c_2832])).
% 4.47/1.74  tff(c_52, plain, (![A_51]: (k2_relat_1(A_51)!=k1_xboole_0 | k1_xboole_0=A_51 | ~v1_relat_1(A_51))), inference(cnfTransformation, [status(thm)], [f_134])).
% 4.47/1.74  tff(c_2988, plain, (k2_relat_1(k3_xboole_0('#skF_4', '#skF_3'))!=k1_xboole_0 | k3_xboole_0('#skF_4', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_2865, c_52])).
% 4.47/1.74  tff(c_2999, plain, (k3_xboole_0('#skF_4', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_2020, c_2988])).
% 4.47/1.74  tff(c_3001, plain, $false, inference(negUnitSimplification, [status(thm)], [c_442, c_2999])).
% 4.47/1.74  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.47/1.74  
% 4.47/1.74  Inference rules
% 4.47/1.74  ----------------------
% 4.47/1.74  #Ref     : 0
% 4.47/1.74  #Sup     : 657
% 4.47/1.74  #Fact    : 0
% 4.47/1.74  #Define  : 0
% 4.47/1.74  #Split   : 6
% 4.47/1.74  #Chain   : 0
% 4.47/1.74  #Close   : 0
% 4.47/1.74  
% 4.47/1.74  Ordering : KBO
% 4.47/1.74  
% 4.47/1.74  Simplification rules
% 4.47/1.74  ----------------------
% 4.47/1.74  #Subsume      : 68
% 4.47/1.74  #Demod        : 467
% 4.47/1.74  #Tautology    : 343
% 4.47/1.74  #SimpNegUnit  : 5
% 4.47/1.74  #BackRed      : 5
% 4.47/1.74  
% 4.47/1.74  #Partial instantiations: 0
% 4.47/1.74  #Strategies tried      : 1
% 4.47/1.74  
% 4.47/1.74  Timing (in seconds)
% 4.47/1.74  ----------------------
% 4.47/1.75  Preprocessing        : 0.32
% 4.47/1.75  Parsing              : 0.18
% 4.47/1.75  CNF conversion       : 0.02
% 4.47/1.75  Main loop            : 0.67
% 4.47/1.75  Inferencing          : 0.22
% 4.47/1.75  Reduction            : 0.21
% 4.47/1.75  Demodulation         : 0.14
% 4.47/1.75  BG Simplification    : 0.03
% 4.47/1.75  Subsumption          : 0.16
% 4.47/1.75  Abstraction          : 0.03
% 4.47/1.75  MUC search           : 0.00
% 4.47/1.75  Cooper               : 0.00
% 4.47/1.75  Total                : 1.02
% 4.47/1.75  Index Insertion      : 0.00
% 4.47/1.75  Index Deletion       : 0.00
% 4.47/1.75  Index Matching       : 0.00
% 4.47/1.75  BG Taut test         : 0.00
%------------------------------------------------------------------------------
