%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:21 EST 2020

% Result     : Theorem 6.62s
% Output     : CNFRefutation 6.68s
% Verified   : 
% Statistics : Number of formulae       :   65 (  95 expanded)
%              Number of leaves         :   36 (  50 expanded)
%              Depth                    :   10
%              Number of atoms          :   76 ( 154 expanded)
%              Number of equality atoms :   21 (  40 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > v1_relat_1 > k6_domain_1 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_8 > #skF_7 > #skF_10 > #skF_13 > #skF_5 > #skF_3 > #skF_9 > #skF_4 > #skF_11 > #skF_2 > #skF_6 > #skF_12

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff('#skF_8',type,(
    '#skF_8': $i > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff('#skF_13',type,(
    '#skF_13': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_11',type,(
    '#skF_11': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_zfmisc_1,type,(
    v1_zfmisc_1: $i > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_6',type,(
    '#skF_6': $i > $i )).

tff('#skF_12',type,(
    '#skF_12': $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_207,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v1_xboole_0(A)
          & v1_zfmisc_1(A) )
       => ! [B] :
            ( ~ v1_xboole_0(k3_xboole_0(A,B))
           => r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tex_2)).

tff(f_51,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_195,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & v1_zfmisc_1(B) )
         => ( r1_tarski(A,B)
           => A = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tex_2)).

tff(f_49,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_74,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_76,axiom,(
    ! [A,B,C] : r1_tarski(k3_xboole_0(A,B),k2_xboole_0(A,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_xboole_1)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C)
        & ! [D] :
            ( ( r1_tarski(D,B)
              & r1_tarski(D,C) )
           => r1_tarski(D,A) ) )
     => A = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_xboole_1)).

tff(f_80,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,k3_xboole_0(C,B)) = k3_xboole_0(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_xboole_1)).

tff(f_82,axiom,(
    ! [A,B,C] : r1_tarski(k2_xboole_0(k3_xboole_0(A,B),k3_xboole_0(A,C)),k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_xboole_1)).

tff(c_98,plain,(
    ~ r1_tarski('#skF_12','#skF_13') ),
    inference(cnfTransformation,[status(thm)],[f_207])).

tff(c_104,plain,(
    ~ v1_xboole_0('#skF_12') ),
    inference(cnfTransformation,[status(thm)],[f_207])).

tff(c_102,plain,(
    v1_zfmisc_1('#skF_12') ),
    inference(cnfTransformation,[status(thm)],[f_207])).

tff(c_22,plain,(
    ! [A_12,B_13] : r1_tarski(k3_xboole_0(A_12,B_13),A_12) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1012,plain,(
    ! [B_163,A_164] :
      ( B_163 = A_164
      | ~ r1_tarski(A_164,B_163)
      | ~ v1_zfmisc_1(B_163)
      | v1_xboole_0(B_163)
      | v1_xboole_0(A_164) ) ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_8804,plain,(
    ! [A_397,B_398] :
      ( k3_xboole_0(A_397,B_398) = A_397
      | ~ v1_zfmisc_1(A_397)
      | v1_xboole_0(A_397)
      | v1_xboole_0(k3_xboole_0(A_397,B_398)) ) ),
    inference(resolution,[status(thm)],[c_22,c_1012])).

tff(c_100,plain,(
    ~ v1_xboole_0(k3_xboole_0('#skF_12','#skF_13')) ),
    inference(cnfTransformation,[status(thm)],[f_207])).

tff(c_8826,plain,
    ( k3_xboole_0('#skF_12','#skF_13') = '#skF_12'
    | ~ v1_zfmisc_1('#skF_12')
    | v1_xboole_0('#skF_12') ),
    inference(resolution,[status(thm)],[c_8804,c_100])).

tff(c_8895,plain,
    ( k3_xboole_0('#skF_12','#skF_13') = '#skF_12'
    | v1_xboole_0('#skF_12') ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_8826])).

tff(c_8896,plain,(
    k3_xboole_0('#skF_12','#skF_13') = '#skF_12' ),
    inference(negUnitSimplification,[status(thm)],[c_104,c_8895])).

tff(c_20,plain,(
    ! [B_11] : r1_tarski(B_11,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_197,plain,(
    ! [A_92,B_93] :
      ( k3_xboole_0(A_92,B_93) = A_92
      | ~ r1_tarski(A_92,B_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_209,plain,(
    ! [B_11] : k3_xboole_0(B_11,B_11) = B_11 ),
    inference(resolution,[status(thm)],[c_20,c_197])).

tff(c_258,plain,(
    ! [A_99,B_100,C_101] : r1_tarski(k3_xboole_0(A_99,B_100),k2_xboole_0(A_99,C_101)) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_267,plain,(
    ! [B_11,C_101] : r1_tarski(B_11,k2_xboole_0(B_11,C_101)) ),
    inference(superposition,[status(thm),theory(equality)],[c_209,c_258])).

tff(c_1743,plain,(
    ! [A_217,B_218,C_219] :
      ( r1_tarski('#skF_5'(A_217,B_218,C_219),C_219)
      | k3_xboole_0(B_218,C_219) = A_217
      | ~ r1_tarski(A_217,C_219)
      | ~ r1_tarski(A_217,B_218) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_26,plain,(
    ! [A_17,B_18,C_19] :
      ( ~ r1_tarski('#skF_5'(A_17,B_18,C_19),A_17)
      | k3_xboole_0(B_18,C_19) = A_17
      | ~ r1_tarski(A_17,C_19)
      | ~ r1_tarski(A_17,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_1754,plain,(
    ! [B_218,C_219] :
      ( k3_xboole_0(B_218,C_219) = C_219
      | ~ r1_tarski(C_219,C_219)
      | ~ r1_tarski(C_219,B_218) ) ),
    inference(resolution,[status(thm)],[c_1743,c_26])).

tff(c_1795,plain,(
    ! [B_220,C_221] :
      ( k3_xboole_0(B_220,C_221) = C_221
      | ~ r1_tarski(C_221,B_220) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_1754])).

tff(c_2044,plain,(
    ! [B_227,C_228] : k3_xboole_0(k2_xboole_0(B_227,C_228),B_227) = B_227 ),
    inference(resolution,[status(thm)],[c_267,c_1795])).

tff(c_36,plain,(
    ! [A_26,C_28,B_27] :
      ( k3_xboole_0(k2_xboole_0(A_26,C_28),B_27) = k2_xboole_0(A_26,k3_xboole_0(C_28,B_27))
      | ~ r1_tarski(A_26,B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_2066,plain,(
    ! [B_227,C_228] :
      ( k2_xboole_0(B_227,k3_xboole_0(C_228,B_227)) = B_227
      | ~ r1_tarski(B_227,B_227) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2044,c_36])).

tff(c_2102,plain,(
    ! [B_227,C_228] : k2_xboole_0(B_227,k3_xboole_0(C_228,B_227)) = B_227 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_2066])).

tff(c_2108,plain,(
    ! [B_229,C_230] : k2_xboole_0(B_229,k3_xboole_0(C_230,B_229)) = B_229 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_2066])).

tff(c_38,plain,(
    ! [A_29,B_30,C_31] : r1_tarski(k2_xboole_0(k3_xboole_0(A_29,B_30),k3_xboole_0(A_29,C_31)),k2_xboole_0(B_30,C_31)) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_2137,plain,(
    ! [C_230,B_30] : r1_tarski(k3_xboole_0(C_230,B_30),k2_xboole_0(B_30,k3_xboole_0(C_230,B_30))) ),
    inference(superposition,[status(thm),theory(equality)],[c_2108,c_38])).

tff(c_2189,plain,(
    ! [C_230,B_30] : r1_tarski(k3_xboole_0(C_230,B_30),B_30) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2102,c_2137])).

tff(c_8999,plain,(
    r1_tarski('#skF_12','#skF_13') ),
    inference(superposition,[status(thm),theory(equality)],[c_8896,c_2189])).

tff(c_9052,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_98,c_8999])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:39:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.62/2.50  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.62/2.51  
% 6.62/2.51  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.62/2.51  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > v1_relat_1 > k6_domain_1 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_8 > #skF_7 > #skF_10 > #skF_13 > #skF_5 > #skF_3 > #skF_9 > #skF_4 > #skF_11 > #skF_2 > #skF_6 > #skF_12
% 6.62/2.51  
% 6.62/2.51  %Foreground sorts:
% 6.62/2.51  
% 6.62/2.51  
% 6.62/2.51  %Background operators:
% 6.62/2.51  
% 6.62/2.51  
% 6.62/2.51  %Foreground operators:
% 6.62/2.51  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.62/2.51  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.62/2.51  tff(k1_tarski, type, k1_tarski: $i > $i).
% 6.62/2.51  tff('#skF_1', type, '#skF_1': $i > $i).
% 6.62/2.51  tff('#skF_8', type, '#skF_8': $i > $i).
% 6.62/2.51  tff('#skF_7', type, '#skF_7': $i).
% 6.62/2.51  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 6.62/2.51  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.62/2.51  tff('#skF_10', type, '#skF_10': $i).
% 6.62/2.51  tff('#skF_13', type, '#skF_13': $i).
% 6.62/2.51  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 6.62/2.51  tff('#skF_3', type, '#skF_3': $i).
% 6.62/2.51  tff('#skF_9', type, '#skF_9': $i).
% 6.62/2.51  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.62/2.51  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.62/2.51  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.62/2.51  tff('#skF_4', type, '#skF_4': $i).
% 6.62/2.51  tff('#skF_11', type, '#skF_11': $i > $i).
% 6.62/2.51  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.62/2.51  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 6.62/2.51  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 6.62/2.51  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 6.62/2.51  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 6.62/2.51  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 6.62/2.51  tff('#skF_6', type, '#skF_6': $i > $i).
% 6.62/2.51  tff('#skF_12', type, '#skF_12': $i).
% 6.62/2.51  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.62/2.51  
% 6.68/2.52  tff(f_207, negated_conjecture, ~(![A]: ((~v1_xboole_0(A) & v1_zfmisc_1(A)) => (![B]: (~v1_xboole_0(k3_xboole_0(A, B)) => r1_tarski(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tex_2)).
% 6.68/2.52  tff(f_51, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 6.68/2.52  tff(f_195, axiom, (![A]: (~v1_xboole_0(A) => (![B]: ((~v1_xboole_0(B) & v1_zfmisc_1(B)) => (r1_tarski(A, B) => (A = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tex_2)).
% 6.68/2.52  tff(f_49, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 6.68/2.52  tff(f_74, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 6.68/2.52  tff(f_76, axiom, (![A, B, C]: r1_tarski(k3_xboole_0(A, B), k2_xboole_0(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_xboole_1)).
% 6.68/2.52  tff(f_70, axiom, (![A, B, C]: (((r1_tarski(A, B) & r1_tarski(A, C)) & (![D]: ((r1_tarski(D, B) & r1_tarski(D, C)) => r1_tarski(D, A)))) => (A = k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_xboole_1)).
% 6.68/2.52  tff(f_80, axiom, (![A, B, C]: (r1_tarski(A, B) => (k2_xboole_0(A, k3_xboole_0(C, B)) = k3_xboole_0(k2_xboole_0(A, C), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t30_xboole_1)).
% 6.68/2.52  tff(f_82, axiom, (![A, B, C]: r1_tarski(k2_xboole_0(k3_xboole_0(A, B), k3_xboole_0(A, C)), k2_xboole_0(B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_xboole_1)).
% 6.68/2.52  tff(c_98, plain, (~r1_tarski('#skF_12', '#skF_13')), inference(cnfTransformation, [status(thm)], [f_207])).
% 6.68/2.52  tff(c_104, plain, (~v1_xboole_0('#skF_12')), inference(cnfTransformation, [status(thm)], [f_207])).
% 6.68/2.52  tff(c_102, plain, (v1_zfmisc_1('#skF_12')), inference(cnfTransformation, [status(thm)], [f_207])).
% 6.68/2.52  tff(c_22, plain, (![A_12, B_13]: (r1_tarski(k3_xboole_0(A_12, B_13), A_12))), inference(cnfTransformation, [status(thm)], [f_51])).
% 6.68/2.52  tff(c_1012, plain, (![B_163, A_164]: (B_163=A_164 | ~r1_tarski(A_164, B_163) | ~v1_zfmisc_1(B_163) | v1_xboole_0(B_163) | v1_xboole_0(A_164))), inference(cnfTransformation, [status(thm)], [f_195])).
% 6.68/2.52  tff(c_8804, plain, (![A_397, B_398]: (k3_xboole_0(A_397, B_398)=A_397 | ~v1_zfmisc_1(A_397) | v1_xboole_0(A_397) | v1_xboole_0(k3_xboole_0(A_397, B_398)))), inference(resolution, [status(thm)], [c_22, c_1012])).
% 6.68/2.52  tff(c_100, plain, (~v1_xboole_0(k3_xboole_0('#skF_12', '#skF_13'))), inference(cnfTransformation, [status(thm)], [f_207])).
% 6.68/2.52  tff(c_8826, plain, (k3_xboole_0('#skF_12', '#skF_13')='#skF_12' | ~v1_zfmisc_1('#skF_12') | v1_xboole_0('#skF_12')), inference(resolution, [status(thm)], [c_8804, c_100])).
% 6.68/2.52  tff(c_8895, plain, (k3_xboole_0('#skF_12', '#skF_13')='#skF_12' | v1_xboole_0('#skF_12')), inference(demodulation, [status(thm), theory('equality')], [c_102, c_8826])).
% 6.68/2.52  tff(c_8896, plain, (k3_xboole_0('#skF_12', '#skF_13')='#skF_12'), inference(negUnitSimplification, [status(thm)], [c_104, c_8895])).
% 6.68/2.52  tff(c_20, plain, (![B_11]: (r1_tarski(B_11, B_11))), inference(cnfTransformation, [status(thm)], [f_49])).
% 6.68/2.52  tff(c_197, plain, (![A_92, B_93]: (k3_xboole_0(A_92, B_93)=A_92 | ~r1_tarski(A_92, B_93))), inference(cnfTransformation, [status(thm)], [f_74])).
% 6.68/2.52  tff(c_209, plain, (![B_11]: (k3_xboole_0(B_11, B_11)=B_11)), inference(resolution, [status(thm)], [c_20, c_197])).
% 6.68/2.52  tff(c_258, plain, (![A_99, B_100, C_101]: (r1_tarski(k3_xboole_0(A_99, B_100), k2_xboole_0(A_99, C_101)))), inference(cnfTransformation, [status(thm)], [f_76])).
% 6.68/2.52  tff(c_267, plain, (![B_11, C_101]: (r1_tarski(B_11, k2_xboole_0(B_11, C_101)))), inference(superposition, [status(thm), theory('equality')], [c_209, c_258])).
% 6.68/2.52  tff(c_1743, plain, (![A_217, B_218, C_219]: (r1_tarski('#skF_5'(A_217, B_218, C_219), C_219) | k3_xboole_0(B_218, C_219)=A_217 | ~r1_tarski(A_217, C_219) | ~r1_tarski(A_217, B_218))), inference(cnfTransformation, [status(thm)], [f_70])).
% 6.68/2.52  tff(c_26, plain, (![A_17, B_18, C_19]: (~r1_tarski('#skF_5'(A_17, B_18, C_19), A_17) | k3_xboole_0(B_18, C_19)=A_17 | ~r1_tarski(A_17, C_19) | ~r1_tarski(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_70])).
% 6.68/2.52  tff(c_1754, plain, (![B_218, C_219]: (k3_xboole_0(B_218, C_219)=C_219 | ~r1_tarski(C_219, C_219) | ~r1_tarski(C_219, B_218))), inference(resolution, [status(thm)], [c_1743, c_26])).
% 6.68/2.52  tff(c_1795, plain, (![B_220, C_221]: (k3_xboole_0(B_220, C_221)=C_221 | ~r1_tarski(C_221, B_220))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_1754])).
% 6.68/2.52  tff(c_2044, plain, (![B_227, C_228]: (k3_xboole_0(k2_xboole_0(B_227, C_228), B_227)=B_227)), inference(resolution, [status(thm)], [c_267, c_1795])).
% 6.68/2.52  tff(c_36, plain, (![A_26, C_28, B_27]: (k3_xboole_0(k2_xboole_0(A_26, C_28), B_27)=k2_xboole_0(A_26, k3_xboole_0(C_28, B_27)) | ~r1_tarski(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_80])).
% 6.68/2.52  tff(c_2066, plain, (![B_227, C_228]: (k2_xboole_0(B_227, k3_xboole_0(C_228, B_227))=B_227 | ~r1_tarski(B_227, B_227))), inference(superposition, [status(thm), theory('equality')], [c_2044, c_36])).
% 6.68/2.52  tff(c_2102, plain, (![B_227, C_228]: (k2_xboole_0(B_227, k3_xboole_0(C_228, B_227))=B_227)), inference(demodulation, [status(thm), theory('equality')], [c_20, c_2066])).
% 6.68/2.52  tff(c_2108, plain, (![B_229, C_230]: (k2_xboole_0(B_229, k3_xboole_0(C_230, B_229))=B_229)), inference(demodulation, [status(thm), theory('equality')], [c_20, c_2066])).
% 6.68/2.52  tff(c_38, plain, (![A_29, B_30, C_31]: (r1_tarski(k2_xboole_0(k3_xboole_0(A_29, B_30), k3_xboole_0(A_29, C_31)), k2_xboole_0(B_30, C_31)))), inference(cnfTransformation, [status(thm)], [f_82])).
% 6.68/2.52  tff(c_2137, plain, (![C_230, B_30]: (r1_tarski(k3_xboole_0(C_230, B_30), k2_xboole_0(B_30, k3_xboole_0(C_230, B_30))))), inference(superposition, [status(thm), theory('equality')], [c_2108, c_38])).
% 6.68/2.52  tff(c_2189, plain, (![C_230, B_30]: (r1_tarski(k3_xboole_0(C_230, B_30), B_30))), inference(demodulation, [status(thm), theory('equality')], [c_2102, c_2137])).
% 6.68/2.52  tff(c_8999, plain, (r1_tarski('#skF_12', '#skF_13')), inference(superposition, [status(thm), theory('equality')], [c_8896, c_2189])).
% 6.68/2.52  tff(c_9052, plain, $false, inference(negUnitSimplification, [status(thm)], [c_98, c_8999])).
% 6.68/2.52  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.68/2.52  
% 6.68/2.52  Inference rules
% 6.68/2.52  ----------------------
% 6.68/2.52  #Ref     : 0
% 6.68/2.52  #Sup     : 2303
% 6.68/2.52  #Fact    : 0
% 6.68/2.52  #Define  : 0
% 6.68/2.52  #Split   : 3
% 6.68/2.52  #Chain   : 0
% 6.68/2.52  #Close   : 0
% 6.68/2.52  
% 6.68/2.52  Ordering : KBO
% 6.68/2.52  
% 6.68/2.52  Simplification rules
% 6.68/2.52  ----------------------
% 6.68/2.52  #Subsume      : 689
% 6.68/2.52  #Demod        : 895
% 6.68/2.52  #Tautology    : 804
% 6.68/2.52  #SimpNegUnit  : 66
% 6.68/2.52  #BackRed      : 9
% 6.68/2.52  
% 6.68/2.52  #Partial instantiations: 0
% 6.68/2.52  #Strategies tried      : 1
% 6.68/2.52  
% 6.68/2.52  Timing (in seconds)
% 6.68/2.52  ----------------------
% 6.68/2.53  Preprocessing        : 0.37
% 6.68/2.53  Parsing              : 0.19
% 6.68/2.53  CNF conversion       : 0.03
% 6.68/2.53  Main loop            : 1.40
% 6.68/2.53  Inferencing          : 0.43
% 6.68/2.53  Reduction            : 0.47
% 6.68/2.53  Demodulation         : 0.34
% 6.68/2.53  BG Simplification    : 0.05
% 6.68/2.53  Subsumption          : 0.34
% 6.68/2.53  Abstraction          : 0.06
% 6.68/2.53  MUC search           : 0.00
% 6.68/2.53  Cooper               : 0.00
% 6.68/2.53  Total                : 1.80
% 6.68/2.53  Index Insertion      : 0.00
% 6.68/2.53  Index Deletion       : 0.00
% 6.68/2.53  Index Matching       : 0.00
% 6.68/2.53  BG Taut test         : 0.00
%------------------------------------------------------------------------------
