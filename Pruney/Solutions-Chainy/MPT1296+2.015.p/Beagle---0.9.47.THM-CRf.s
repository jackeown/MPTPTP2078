%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:42 EST 2020

% Result     : Theorem 4.59s
% Output     : CNFRefutation 4.66s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 136 expanded)
%              Number of leaves         :   25 (  55 expanded)
%              Depth                    :   10
%              Number of atoms          :  119 ( 261 expanded)
%              Number of equality atoms :   43 (  78 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > k7_setfam_1 > k6_setfam_1 > k5_setfam_1 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k7_setfam_1,type,(
    k7_setfam_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k5_setfam_1,type,(
    k5_setfam_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k6_setfam_1,type,(
    k6_setfam_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_87,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
       => ( B != k1_xboole_0
         => k5_setfam_1(A,k7_setfam_1(A,B)) = k3_subset_1(A,k6_setfam_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_tops_2)).

tff(f_53,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => m1_subset_1(k7_setfam_1(A,B),k1_zfmisc_1(k1_zfmisc_1(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_setfam_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_31,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(A)))
         => ( C = k7_setfam_1(A,B)
          <=> ! [D] :
                ( m1_subset_1(D,k1_zfmisc_1(A))
               => ( r2_hidden(D,C)
                <=> r2_hidden(k3_subset_1(A,D),B) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_setfam_1)).

tff(f_72,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => k7_setfam_1(A,k7_setfam_1(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k7_setfam_1)).

tff(f_79,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ( B != k1_xboole_0
       => k6_setfam_1(A,k7_setfam_1(A,B)) = k3_subset_1(A,k5_setfam_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_tops_2)).

tff(f_49,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => m1_subset_1(k5_setfam_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_setfam_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(c_40,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_252,plain,(
    ! [A_63,B_64] :
      ( m1_subset_1(k7_setfam_1(A_63,B_64),k1_zfmisc_1(k1_zfmisc_1(A_63)))
      | ~ m1_subset_1(B_64,k1_zfmisc_1(k1_zfmisc_1(A_63))) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_26,plain,(
    ! [A_21,B_22] :
      ( r1_tarski(A_21,B_22)
      | ~ m1_subset_1(A_21,k1_zfmisc_1(B_22)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_271,plain,(
    ! [A_63,B_64] :
      ( r1_tarski(k7_setfam_1(A_63,B_64),k1_zfmisc_1(A_63))
      | ~ m1_subset_1(B_64,k1_zfmisc_1(k1_zfmisc_1(A_63))) ) ),
    inference(resolution,[status(thm)],[c_252,c_26])).

tff(c_36,plain,(
    k5_setfam_1('#skF_2',k7_setfam_1('#skF_2','#skF_3')) != k3_subset_1('#skF_2',k6_setfam_1('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_38,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_4,plain,(
    ! [A_3] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_3)) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_43,plain,(
    ! [A_33,B_34] :
      ( r1_tarski(A_33,B_34)
      | ~ m1_subset_1(A_33,k1_zfmisc_1(B_34)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_51,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(resolution,[status(thm)],[c_4,c_43])).

tff(c_817,plain,(
    ! [A_109,B_110,C_111] :
      ( r2_hidden('#skF_1'(A_109,B_110,C_111),C_111)
      | r2_hidden(k3_subset_1(A_109,'#skF_1'(A_109,B_110,C_111)),B_110)
      | k7_setfam_1(A_109,B_110) = C_111
      | ~ m1_subset_1(C_111,k1_zfmisc_1(k1_zfmisc_1(A_109)))
      | ~ m1_subset_1(B_110,k1_zfmisc_1(k1_zfmisc_1(A_109))) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_32,plain,(
    ! [B_27,A_26] :
      ( ~ r1_tarski(B_27,A_26)
      | ~ r2_hidden(A_26,B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_2261,plain,(
    ! [B_180,A_181,C_182] :
      ( ~ r1_tarski(B_180,k3_subset_1(A_181,'#skF_1'(A_181,B_180,C_182)))
      | r2_hidden('#skF_1'(A_181,B_180,C_182),C_182)
      | k7_setfam_1(A_181,B_180) = C_182
      | ~ m1_subset_1(C_182,k1_zfmisc_1(k1_zfmisc_1(A_181)))
      | ~ m1_subset_1(B_180,k1_zfmisc_1(k1_zfmisc_1(A_181))) ) ),
    inference(resolution,[status(thm)],[c_817,c_32])).

tff(c_2264,plain,(
    ! [A_181,C_182] :
      ( r2_hidden('#skF_1'(A_181,k1_xboole_0,C_182),C_182)
      | k7_setfam_1(A_181,k1_xboole_0) = C_182
      | ~ m1_subset_1(C_182,k1_zfmisc_1(k1_zfmisc_1(A_181)))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(A_181))) ) ),
    inference(resolution,[status(thm)],[c_51,c_2261])).

tff(c_2274,plain,(
    ! [A_183,C_184] :
      ( r2_hidden('#skF_1'(A_183,k1_xboole_0,C_184),C_184)
      | k7_setfam_1(A_183,k1_xboole_0) = C_184
      | ~ m1_subset_1(C_184,k1_zfmisc_1(k1_zfmisc_1(A_183))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_2264])).

tff(c_2299,plain,(
    ! [A_185] :
      ( r2_hidden('#skF_1'(A_185,k1_xboole_0,k1_xboole_0),k1_xboole_0)
      | k7_setfam_1(A_185,k1_xboole_0) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_2274])).

tff(c_2309,plain,(
    ! [A_185] :
      ( ~ r1_tarski(k1_xboole_0,'#skF_1'(A_185,k1_xboole_0,k1_xboole_0))
      | k7_setfam_1(A_185,k1_xboole_0) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_2299,c_32])).

tff(c_2324,plain,(
    ! [A_186] : k7_setfam_1(A_186,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_51,c_2309])).

tff(c_373,plain,(
    ! [A_77,B_78,C_79] :
      ( m1_subset_1('#skF_1'(A_77,B_78,C_79),k1_zfmisc_1(A_77))
      | k7_setfam_1(A_77,B_78) = C_79
      | ~ m1_subset_1(C_79,k1_zfmisc_1(k1_zfmisc_1(A_77)))
      | ~ m1_subset_1(B_78,k1_zfmisc_1(k1_zfmisc_1(A_77))) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1117,plain,(
    ! [A_131,B_132,C_133] :
      ( r1_tarski('#skF_1'(A_131,B_132,C_133),A_131)
      | k7_setfam_1(A_131,B_132) = C_133
      | ~ m1_subset_1(C_133,k1_zfmisc_1(k1_zfmisc_1(A_131)))
      | ~ m1_subset_1(B_132,k1_zfmisc_1(k1_zfmisc_1(A_131))) ) ),
    inference(resolution,[status(thm)],[c_373,c_26])).

tff(c_1148,plain,(
    ! [B_135] :
      ( r1_tarski('#skF_1'('#skF_2',B_135,'#skF_3'),'#skF_2')
      | k7_setfam_1('#skF_2',B_135) = '#skF_3'
      | ~ m1_subset_1(B_135,k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_40,c_1117])).

tff(c_1177,plain,
    ( r1_tarski('#skF_1'('#skF_2',k1_xboole_0,'#skF_3'),'#skF_2')
    | k7_setfam_1('#skF_2',k1_xboole_0) = '#skF_3' ),
    inference(resolution,[status(thm)],[c_4,c_1148])).

tff(c_1279,plain,(
    k7_setfam_1('#skF_2',k1_xboole_0) = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_1177])).

tff(c_2343,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_2324,c_1279])).

tff(c_2376,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_2343])).

tff(c_2378,plain,(
    k7_setfam_1('#skF_2',k1_xboole_0) != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_1177])).

tff(c_2389,plain,(
    ! [A_192,B_193] :
      ( r1_tarski('#skF_1'(A_192,B_193,k1_xboole_0),A_192)
      | k7_setfam_1(A_192,B_193) = k1_xboole_0
      | ~ m1_subset_1(B_193,k1_zfmisc_1(k1_zfmisc_1(A_192))) ) ),
    inference(resolution,[status(thm)],[c_4,c_1117])).

tff(c_2410,plain,
    ( r1_tarski('#skF_1'('#skF_2','#skF_3',k1_xboole_0),'#skF_2')
    | k7_setfam_1('#skF_2','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_40,c_2389])).

tff(c_2412,plain,(
    k7_setfam_1('#skF_2','#skF_3') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_2410])).

tff(c_140,plain,(
    ! [A_48,B_49] :
      ( k7_setfam_1(A_48,k7_setfam_1(A_48,B_49)) = B_49
      | ~ m1_subset_1(B_49,k1_zfmisc_1(k1_zfmisc_1(A_48))) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_150,plain,(
    k7_setfam_1('#skF_2',k7_setfam_1('#skF_2','#skF_3')) = '#skF_3' ),
    inference(resolution,[status(thm)],[c_40,c_140])).

tff(c_2419,plain,(
    k7_setfam_1('#skF_2',k1_xboole_0) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2412,c_150])).

tff(c_2422,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2378,c_2419])).

tff(c_2424,plain,(
    k7_setfam_1('#skF_2','#skF_3') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_2410])).

tff(c_22,plain,(
    ! [A_17,B_18] :
      ( m1_subset_1(k7_setfam_1(A_17,B_18),k1_zfmisc_1(k1_zfmisc_1(A_17)))
      | ~ m1_subset_1(B_18,k1_zfmisc_1(k1_zfmisc_1(A_17))) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_298,plain,(
    ! [A_68,B_69] :
      ( k6_setfam_1(A_68,k7_setfam_1(A_68,B_69)) = k3_subset_1(A_68,k5_setfam_1(A_68,B_69))
      | k1_xboole_0 = B_69
      | ~ m1_subset_1(B_69,k1_zfmisc_1(k1_zfmisc_1(A_68))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_2443,plain,(
    ! [A_197,B_198] :
      ( k6_setfam_1(A_197,k7_setfam_1(A_197,k7_setfam_1(A_197,B_198))) = k3_subset_1(A_197,k5_setfam_1(A_197,k7_setfam_1(A_197,B_198)))
      | k7_setfam_1(A_197,B_198) = k1_xboole_0
      | ~ m1_subset_1(B_198,k1_zfmisc_1(k1_zfmisc_1(A_197))) ) ),
    inference(resolution,[status(thm)],[c_22,c_298])).

tff(c_2456,plain,
    ( k6_setfam_1('#skF_2',k7_setfam_1('#skF_2',k7_setfam_1('#skF_2','#skF_3'))) = k3_subset_1('#skF_2',k5_setfam_1('#skF_2',k7_setfam_1('#skF_2','#skF_3')))
    | k7_setfam_1('#skF_2','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_40,c_2443])).

tff(c_2465,plain,
    ( k3_subset_1('#skF_2',k5_setfam_1('#skF_2',k7_setfam_1('#skF_2','#skF_3'))) = k6_setfam_1('#skF_2','#skF_3')
    | k7_setfam_1('#skF_2','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_150,c_2456])).

tff(c_2466,plain,(
    k3_subset_1('#skF_2',k5_setfam_1('#skF_2',k7_setfam_1('#skF_2','#skF_3'))) = k6_setfam_1('#skF_2','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_2424,c_2465])).

tff(c_28,plain,(
    ! [A_21,B_22] :
      ( m1_subset_1(A_21,k1_zfmisc_1(B_22))
      | ~ r1_tarski(A_21,B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_237,plain,(
    ! [A_61,B_62] :
      ( m1_subset_1(k5_setfam_1(A_61,B_62),k1_zfmisc_1(A_61))
      | ~ m1_subset_1(B_62,k1_zfmisc_1(k1_zfmisc_1(A_61))) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k3_subset_1(A_1,k3_subset_1(A_1,B_2)) = B_2
      | ~ m1_subset_1(B_2,k1_zfmisc_1(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_428,plain,(
    ! [A_91,B_92] :
      ( k3_subset_1(A_91,k3_subset_1(A_91,k5_setfam_1(A_91,B_92))) = k5_setfam_1(A_91,B_92)
      | ~ m1_subset_1(B_92,k1_zfmisc_1(k1_zfmisc_1(A_91))) ) ),
    inference(resolution,[status(thm)],[c_237,c_2])).

tff(c_448,plain,(
    ! [A_91,A_21] :
      ( k3_subset_1(A_91,k3_subset_1(A_91,k5_setfam_1(A_91,A_21))) = k5_setfam_1(A_91,A_21)
      | ~ r1_tarski(A_21,k1_zfmisc_1(A_91)) ) ),
    inference(resolution,[status(thm)],[c_28,c_428])).

tff(c_2477,plain,
    ( k5_setfam_1('#skF_2',k7_setfam_1('#skF_2','#skF_3')) = k3_subset_1('#skF_2',k6_setfam_1('#skF_2','#skF_3'))
    | ~ r1_tarski(k7_setfam_1('#skF_2','#skF_3'),k1_zfmisc_1('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2466,c_448])).

tff(c_2486,plain,(
    ~ r1_tarski(k7_setfam_1('#skF_2','#skF_3'),k1_zfmisc_1('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_2477])).

tff(c_2492,plain,(
    ~ m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_271,c_2486])).

tff(c_2496,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_2492])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.33  % Computer   : n008.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % DateTime   : Tue Dec  1 13:27:30 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.59/1.79  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.59/1.79  
% 4.59/1.79  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.59/1.79  %$ r2_hidden > r1_tarski > m1_subset_1 > k7_setfam_1 > k6_setfam_1 > k5_setfam_1 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3
% 4.59/1.79  
% 4.59/1.79  %Foreground sorts:
% 4.59/1.79  
% 4.59/1.79  
% 4.59/1.79  %Background operators:
% 4.59/1.79  
% 4.59/1.79  
% 4.59/1.79  %Foreground operators:
% 4.59/1.79  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 4.59/1.79  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.59/1.79  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.59/1.79  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.59/1.79  tff(k7_setfam_1, type, k7_setfam_1: ($i * $i) > $i).
% 4.59/1.79  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.59/1.79  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 4.59/1.79  tff('#skF_2', type, '#skF_2': $i).
% 4.59/1.79  tff('#skF_3', type, '#skF_3': $i).
% 4.59/1.79  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.59/1.79  tff(k5_setfam_1, type, k5_setfam_1: ($i * $i) > $i).
% 4.59/1.79  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.59/1.79  tff(k6_setfam_1, type, k6_setfam_1: ($i * $i) > $i).
% 4.59/1.79  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.59/1.79  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.59/1.79  
% 4.66/1.81  tff(f_87, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (~(B = k1_xboole_0) => (k5_setfam_1(A, k7_setfam_1(A, B)) = k3_subset_1(A, k6_setfam_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_tops_2)).
% 4.66/1.81  tff(f_53, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => m1_subset_1(k7_setfam_1(A, B), k1_zfmisc_1(k1_zfmisc_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_setfam_1)).
% 4.66/1.81  tff(f_61, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 4.66/1.81  tff(f_31, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 4.66/1.81  tff(f_45, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(A))) => ((C = k7_setfam_1(A, B)) <=> (![D]: (m1_subset_1(D, k1_zfmisc_1(A)) => (r2_hidden(D, C) <=> r2_hidden(k3_subset_1(A, D), B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_setfam_1)).
% 4.66/1.81  tff(f_72, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 4.66/1.81  tff(f_57, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (k7_setfam_1(A, k7_setfam_1(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k7_setfam_1)).
% 4.66/1.81  tff(f_79, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (~(B = k1_xboole_0) => (k6_setfam_1(A, k7_setfam_1(A, B)) = k3_subset_1(A, k5_setfam_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_tops_2)).
% 4.66/1.81  tff(f_49, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => m1_subset_1(k5_setfam_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k5_setfam_1)).
% 4.66/1.81  tff(f_29, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 4.66/1.81  tff(c_40, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_87])).
% 4.66/1.81  tff(c_252, plain, (![A_63, B_64]: (m1_subset_1(k7_setfam_1(A_63, B_64), k1_zfmisc_1(k1_zfmisc_1(A_63))) | ~m1_subset_1(B_64, k1_zfmisc_1(k1_zfmisc_1(A_63))))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.66/1.81  tff(c_26, plain, (![A_21, B_22]: (r1_tarski(A_21, B_22) | ~m1_subset_1(A_21, k1_zfmisc_1(B_22)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.66/1.81  tff(c_271, plain, (![A_63, B_64]: (r1_tarski(k7_setfam_1(A_63, B_64), k1_zfmisc_1(A_63)) | ~m1_subset_1(B_64, k1_zfmisc_1(k1_zfmisc_1(A_63))))), inference(resolution, [status(thm)], [c_252, c_26])).
% 4.66/1.81  tff(c_36, plain, (k5_setfam_1('#skF_2', k7_setfam_1('#skF_2', '#skF_3'))!=k3_subset_1('#skF_2', k6_setfam_1('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_87])).
% 4.66/1.81  tff(c_38, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_87])).
% 4.66/1.81  tff(c_4, plain, (![A_3]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.66/1.81  tff(c_43, plain, (![A_33, B_34]: (r1_tarski(A_33, B_34) | ~m1_subset_1(A_33, k1_zfmisc_1(B_34)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.66/1.81  tff(c_51, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(resolution, [status(thm)], [c_4, c_43])).
% 4.66/1.81  tff(c_817, plain, (![A_109, B_110, C_111]: (r2_hidden('#skF_1'(A_109, B_110, C_111), C_111) | r2_hidden(k3_subset_1(A_109, '#skF_1'(A_109, B_110, C_111)), B_110) | k7_setfam_1(A_109, B_110)=C_111 | ~m1_subset_1(C_111, k1_zfmisc_1(k1_zfmisc_1(A_109))) | ~m1_subset_1(B_110, k1_zfmisc_1(k1_zfmisc_1(A_109))))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.66/1.81  tff(c_32, plain, (![B_27, A_26]: (~r1_tarski(B_27, A_26) | ~r2_hidden(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.66/1.81  tff(c_2261, plain, (![B_180, A_181, C_182]: (~r1_tarski(B_180, k3_subset_1(A_181, '#skF_1'(A_181, B_180, C_182))) | r2_hidden('#skF_1'(A_181, B_180, C_182), C_182) | k7_setfam_1(A_181, B_180)=C_182 | ~m1_subset_1(C_182, k1_zfmisc_1(k1_zfmisc_1(A_181))) | ~m1_subset_1(B_180, k1_zfmisc_1(k1_zfmisc_1(A_181))))), inference(resolution, [status(thm)], [c_817, c_32])).
% 4.66/1.81  tff(c_2264, plain, (![A_181, C_182]: (r2_hidden('#skF_1'(A_181, k1_xboole_0, C_182), C_182) | k7_setfam_1(A_181, k1_xboole_0)=C_182 | ~m1_subset_1(C_182, k1_zfmisc_1(k1_zfmisc_1(A_181))) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_zfmisc_1(A_181))))), inference(resolution, [status(thm)], [c_51, c_2261])).
% 4.66/1.81  tff(c_2274, plain, (![A_183, C_184]: (r2_hidden('#skF_1'(A_183, k1_xboole_0, C_184), C_184) | k7_setfam_1(A_183, k1_xboole_0)=C_184 | ~m1_subset_1(C_184, k1_zfmisc_1(k1_zfmisc_1(A_183))))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_2264])).
% 4.66/1.81  tff(c_2299, plain, (![A_185]: (r2_hidden('#skF_1'(A_185, k1_xboole_0, k1_xboole_0), k1_xboole_0) | k7_setfam_1(A_185, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_2274])).
% 4.66/1.81  tff(c_2309, plain, (![A_185]: (~r1_tarski(k1_xboole_0, '#skF_1'(A_185, k1_xboole_0, k1_xboole_0)) | k7_setfam_1(A_185, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_2299, c_32])).
% 4.66/1.81  tff(c_2324, plain, (![A_186]: (k7_setfam_1(A_186, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_51, c_2309])).
% 4.66/1.81  tff(c_373, plain, (![A_77, B_78, C_79]: (m1_subset_1('#skF_1'(A_77, B_78, C_79), k1_zfmisc_1(A_77)) | k7_setfam_1(A_77, B_78)=C_79 | ~m1_subset_1(C_79, k1_zfmisc_1(k1_zfmisc_1(A_77))) | ~m1_subset_1(B_78, k1_zfmisc_1(k1_zfmisc_1(A_77))))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.66/1.81  tff(c_1117, plain, (![A_131, B_132, C_133]: (r1_tarski('#skF_1'(A_131, B_132, C_133), A_131) | k7_setfam_1(A_131, B_132)=C_133 | ~m1_subset_1(C_133, k1_zfmisc_1(k1_zfmisc_1(A_131))) | ~m1_subset_1(B_132, k1_zfmisc_1(k1_zfmisc_1(A_131))))), inference(resolution, [status(thm)], [c_373, c_26])).
% 4.66/1.81  tff(c_1148, plain, (![B_135]: (r1_tarski('#skF_1'('#skF_2', B_135, '#skF_3'), '#skF_2') | k7_setfam_1('#skF_2', B_135)='#skF_3' | ~m1_subset_1(B_135, k1_zfmisc_1(k1_zfmisc_1('#skF_2'))))), inference(resolution, [status(thm)], [c_40, c_1117])).
% 4.66/1.81  tff(c_1177, plain, (r1_tarski('#skF_1'('#skF_2', k1_xboole_0, '#skF_3'), '#skF_2') | k7_setfam_1('#skF_2', k1_xboole_0)='#skF_3'), inference(resolution, [status(thm)], [c_4, c_1148])).
% 4.66/1.81  tff(c_1279, plain, (k7_setfam_1('#skF_2', k1_xboole_0)='#skF_3'), inference(splitLeft, [status(thm)], [c_1177])).
% 4.66/1.81  tff(c_2343, plain, (k1_xboole_0='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_2324, c_1279])).
% 4.66/1.81  tff(c_2376, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_2343])).
% 4.66/1.81  tff(c_2378, plain, (k7_setfam_1('#skF_2', k1_xboole_0)!='#skF_3'), inference(splitRight, [status(thm)], [c_1177])).
% 4.66/1.81  tff(c_2389, plain, (![A_192, B_193]: (r1_tarski('#skF_1'(A_192, B_193, k1_xboole_0), A_192) | k7_setfam_1(A_192, B_193)=k1_xboole_0 | ~m1_subset_1(B_193, k1_zfmisc_1(k1_zfmisc_1(A_192))))), inference(resolution, [status(thm)], [c_4, c_1117])).
% 4.66/1.81  tff(c_2410, plain, (r1_tarski('#skF_1'('#skF_2', '#skF_3', k1_xboole_0), '#skF_2') | k7_setfam_1('#skF_2', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_40, c_2389])).
% 4.66/1.81  tff(c_2412, plain, (k7_setfam_1('#skF_2', '#skF_3')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_2410])).
% 4.66/1.81  tff(c_140, plain, (![A_48, B_49]: (k7_setfam_1(A_48, k7_setfam_1(A_48, B_49))=B_49 | ~m1_subset_1(B_49, k1_zfmisc_1(k1_zfmisc_1(A_48))))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.66/1.81  tff(c_150, plain, (k7_setfam_1('#skF_2', k7_setfam_1('#skF_2', '#skF_3'))='#skF_3'), inference(resolution, [status(thm)], [c_40, c_140])).
% 4.66/1.81  tff(c_2419, plain, (k7_setfam_1('#skF_2', k1_xboole_0)='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_2412, c_150])).
% 4.66/1.81  tff(c_2422, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2378, c_2419])).
% 4.66/1.81  tff(c_2424, plain, (k7_setfam_1('#skF_2', '#skF_3')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_2410])).
% 4.66/1.81  tff(c_22, plain, (![A_17, B_18]: (m1_subset_1(k7_setfam_1(A_17, B_18), k1_zfmisc_1(k1_zfmisc_1(A_17))) | ~m1_subset_1(B_18, k1_zfmisc_1(k1_zfmisc_1(A_17))))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.66/1.81  tff(c_298, plain, (![A_68, B_69]: (k6_setfam_1(A_68, k7_setfam_1(A_68, B_69))=k3_subset_1(A_68, k5_setfam_1(A_68, B_69)) | k1_xboole_0=B_69 | ~m1_subset_1(B_69, k1_zfmisc_1(k1_zfmisc_1(A_68))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 4.66/1.81  tff(c_2443, plain, (![A_197, B_198]: (k6_setfam_1(A_197, k7_setfam_1(A_197, k7_setfam_1(A_197, B_198)))=k3_subset_1(A_197, k5_setfam_1(A_197, k7_setfam_1(A_197, B_198))) | k7_setfam_1(A_197, B_198)=k1_xboole_0 | ~m1_subset_1(B_198, k1_zfmisc_1(k1_zfmisc_1(A_197))))), inference(resolution, [status(thm)], [c_22, c_298])).
% 4.66/1.81  tff(c_2456, plain, (k6_setfam_1('#skF_2', k7_setfam_1('#skF_2', k7_setfam_1('#skF_2', '#skF_3')))=k3_subset_1('#skF_2', k5_setfam_1('#skF_2', k7_setfam_1('#skF_2', '#skF_3'))) | k7_setfam_1('#skF_2', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_40, c_2443])).
% 4.66/1.81  tff(c_2465, plain, (k3_subset_1('#skF_2', k5_setfam_1('#skF_2', k7_setfam_1('#skF_2', '#skF_3')))=k6_setfam_1('#skF_2', '#skF_3') | k7_setfam_1('#skF_2', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_150, c_2456])).
% 4.66/1.81  tff(c_2466, plain, (k3_subset_1('#skF_2', k5_setfam_1('#skF_2', k7_setfam_1('#skF_2', '#skF_3')))=k6_setfam_1('#skF_2', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_2424, c_2465])).
% 4.66/1.81  tff(c_28, plain, (![A_21, B_22]: (m1_subset_1(A_21, k1_zfmisc_1(B_22)) | ~r1_tarski(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.66/1.81  tff(c_237, plain, (![A_61, B_62]: (m1_subset_1(k5_setfam_1(A_61, B_62), k1_zfmisc_1(A_61)) | ~m1_subset_1(B_62, k1_zfmisc_1(k1_zfmisc_1(A_61))))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.66/1.81  tff(c_2, plain, (![A_1, B_2]: (k3_subset_1(A_1, k3_subset_1(A_1, B_2))=B_2 | ~m1_subset_1(B_2, k1_zfmisc_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.66/1.81  tff(c_428, plain, (![A_91, B_92]: (k3_subset_1(A_91, k3_subset_1(A_91, k5_setfam_1(A_91, B_92)))=k5_setfam_1(A_91, B_92) | ~m1_subset_1(B_92, k1_zfmisc_1(k1_zfmisc_1(A_91))))), inference(resolution, [status(thm)], [c_237, c_2])).
% 4.66/1.81  tff(c_448, plain, (![A_91, A_21]: (k3_subset_1(A_91, k3_subset_1(A_91, k5_setfam_1(A_91, A_21)))=k5_setfam_1(A_91, A_21) | ~r1_tarski(A_21, k1_zfmisc_1(A_91)))), inference(resolution, [status(thm)], [c_28, c_428])).
% 4.66/1.81  tff(c_2477, plain, (k5_setfam_1('#skF_2', k7_setfam_1('#skF_2', '#skF_3'))=k3_subset_1('#skF_2', k6_setfam_1('#skF_2', '#skF_3')) | ~r1_tarski(k7_setfam_1('#skF_2', '#skF_3'), k1_zfmisc_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_2466, c_448])).
% 4.66/1.81  tff(c_2486, plain, (~r1_tarski(k7_setfam_1('#skF_2', '#skF_3'), k1_zfmisc_1('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_36, c_2477])).
% 4.66/1.81  tff(c_2492, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1('#skF_2')))), inference(resolution, [status(thm)], [c_271, c_2486])).
% 4.66/1.81  tff(c_2496, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_2492])).
% 4.66/1.81  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.66/1.81  
% 4.66/1.81  Inference rules
% 4.66/1.81  ----------------------
% 4.66/1.81  #Ref     : 0
% 4.66/1.81  #Sup     : 567
% 4.66/1.81  #Fact    : 0
% 4.66/1.81  #Define  : 0
% 4.66/1.81  #Split   : 8
% 4.66/1.81  #Chain   : 0
% 4.66/1.81  #Close   : 0
% 4.66/1.81  
% 4.66/1.81  Ordering : KBO
% 4.66/1.81  
% 4.66/1.81  Simplification rules
% 4.66/1.81  ----------------------
% 4.66/1.81  #Subsume      : 75
% 4.66/1.81  #Demod        : 313
% 4.66/1.81  #Tautology    : 209
% 4.66/1.81  #SimpNegUnit  : 19
% 4.66/1.81  #BackRed      : 36
% 4.66/1.81  
% 4.66/1.81  #Partial instantiations: 0
% 4.66/1.81  #Strategies tried      : 1
% 4.66/1.81  
% 4.66/1.81  Timing (in seconds)
% 4.66/1.81  ----------------------
% 4.66/1.81  Preprocessing        : 0.31
% 4.66/1.81  Parsing              : 0.16
% 4.66/1.81  CNF conversion       : 0.02
% 4.66/1.81  Main loop            : 0.74
% 4.66/1.81  Inferencing          : 0.25
% 4.66/1.81  Reduction            : 0.23
% 4.66/1.81  Demodulation         : 0.17
% 4.66/1.81  BG Simplification    : 0.03
% 4.66/1.81  Subsumption          : 0.15
% 4.66/1.81  Abstraction          : 0.04
% 4.66/1.81  MUC search           : 0.00
% 4.66/1.81  Cooper               : 0.00
% 4.66/1.81  Total                : 1.09
% 4.66/1.81  Index Insertion      : 0.00
% 4.66/1.81  Index Deletion       : 0.00
% 4.66/1.81  Index Matching       : 0.00
% 4.75/1.81  BG Taut test         : 0.00
%------------------------------------------------------------------------------
