%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:24 EST 2020

% Result     : Theorem 2.12s
% Output     : CNFRefutation 2.23s
% Verified   : 
% Statistics : Number of formulae       :   53 (  60 expanded)
%              Number of leaves         :   24 (  31 expanded)
%              Depth                    :    9
%              Number of atoms          :   67 (  86 expanded)
%              Number of equality atoms :   29 (  33 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_zfmisc_1 > v1_xboole_0 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_zfmisc_1,type,(
    v1_zfmisc_1: $i > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_35,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_74,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v1_xboole_0(A)
          & v1_zfmisc_1(A) )
       => ! [B] :
            ( ~ v1_xboole_0(k3_xboole_0(A,B))
           => r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tex_2)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] : k3_xboole_0(A,k2_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_62,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & v1_zfmisc_1(B) )
         => ( r1_tarski(A,B)
           => A = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tex_2)).

tff(c_94,plain,(
    ! [A_36,B_37] :
      ( r1_tarski(A_36,B_37)
      | k4_xboole_0(A_36,B_37) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_26,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_102,plain,(
    k4_xboole_0('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_94,c_26])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_115,plain,(
    ! [A_40,C_41,B_42] :
      ( r1_tarski(A_40,C_41)
      | ~ r1_tarski(k2_xboole_0(A_40,B_42),C_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_126,plain,(
    ! [A_43,B_44] : r1_tarski(A_43,k2_xboole_0(A_43,B_44)) ),
    inference(resolution,[status(thm)],[c_6,c_115])).

tff(c_10,plain,(
    ! [A_3,B_4] :
      ( k4_xboole_0(A_3,B_4) = k1_xboole_0
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_135,plain,(
    ! [A_43,B_44] : k4_xboole_0(A_43,k2_xboole_0(A_43,B_44)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_126,c_10])).

tff(c_18,plain,(
    ! [A_12,B_13] : k3_xboole_0(A_12,k2_xboole_0(A_12,B_13)) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_103,plain,(
    ! [A_38,B_39] : k5_xboole_0(A_38,k3_xboole_0(A_38,B_39)) = k4_xboole_0(A_38,B_39) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_112,plain,(
    ! [A_12,B_13] : k4_xboole_0(A_12,k2_xboole_0(A_12,B_13)) = k5_xboole_0(A_12,A_12) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_103])).

tff(c_172,plain,(
    ! [A_12] : k5_xboole_0(A_12,A_12) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_135,c_112])).

tff(c_16,plain,(
    ! [A_10,B_11] : r1_tarski(k3_xboole_0(A_10,B_11),A_10) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_67,plain,(
    ! [A_31,B_32] :
      ( k4_xboole_0(A_31,B_32) = k1_xboole_0
      | ~ r1_tarski(A_31,B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_74,plain,(
    ! [A_10,B_11] : k4_xboole_0(k3_xboole_0(A_10,B_11),A_10) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_16,c_67])).

tff(c_32,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_30,plain,(
    v1_zfmisc_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r1_tarski(A_3,B_4)
      | k4_xboole_0(A_3,B_4) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_240,plain,(
    ! [B_63,A_64] :
      ( B_63 = A_64
      | ~ r1_tarski(A_64,B_63)
      | ~ v1_zfmisc_1(B_63)
      | v1_xboole_0(B_63)
      | v1_xboole_0(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_313,plain,(
    ! [B_77,A_78] :
      ( B_77 = A_78
      | ~ v1_zfmisc_1(B_77)
      | v1_xboole_0(B_77)
      | v1_xboole_0(A_78)
      | k4_xboole_0(A_78,B_77) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_240])).

tff(c_315,plain,(
    ! [A_78] :
      ( A_78 = '#skF_1'
      | v1_xboole_0('#skF_1')
      | v1_xboole_0(A_78)
      | k4_xboole_0(A_78,'#skF_1') != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_30,c_313])).

tff(c_319,plain,(
    ! [A_79] :
      ( A_79 = '#skF_1'
      | v1_xboole_0(A_79)
      | k4_xboole_0(A_79,'#skF_1') != k1_xboole_0 ) ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_315])).

tff(c_28,plain,(
    ~ v1_xboole_0(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_322,plain,
    ( k3_xboole_0('#skF_1','#skF_2') = '#skF_1'
    | k4_xboole_0(k3_xboole_0('#skF_1','#skF_2'),'#skF_1') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_319,c_28])).

tff(c_328,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_322])).

tff(c_12,plain,(
    ! [A_5,B_6] : k5_xboole_0(A_5,k3_xboole_0(A_5,B_6)) = k4_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_343,plain,(
    k5_xboole_0('#skF_1','#skF_1') = k4_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_328,c_12])).

tff(c_356,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_172,c_343])).

tff(c_358,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_102,c_356])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n001.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 18:36:00 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.12/1.28  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.23/1.28  
% 2.23/1.28  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.23/1.28  %$ r1_tarski > v1_zfmisc_1 > v1_xboole_0 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1
% 2.23/1.28  
% 2.23/1.28  %Foreground sorts:
% 2.23/1.28  
% 2.23/1.28  
% 2.23/1.28  %Background operators:
% 2.23/1.28  
% 2.23/1.28  
% 2.23/1.28  %Foreground operators:
% 2.23/1.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.23/1.28  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.23/1.28  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.23/1.28  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.23/1.28  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.23/1.28  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.23/1.28  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.23/1.28  tff('#skF_2', type, '#skF_2': $i).
% 2.23/1.28  tff('#skF_1', type, '#skF_1': $i).
% 2.23/1.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.23/1.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.23/1.28  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 2.23/1.28  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.23/1.28  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.23/1.28  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.23/1.28  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.23/1.28  
% 2.23/1.30  tff(f_35, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.23/1.30  tff(f_74, negated_conjecture, ~(![A]: ((~v1_xboole_0(A) & v1_zfmisc_1(A)) => (![B]: (~v1_xboole_0(k3_xboole_0(A, B)) => r1_tarski(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tex_2)).
% 2.23/1.30  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.23/1.30  tff(f_41, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_xboole_1)).
% 2.23/1.30  tff(f_45, axiom, (![A, B]: (k3_xboole_0(A, k2_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_xboole_1)).
% 2.23/1.30  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.23/1.30  tff(f_43, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 2.23/1.30  tff(f_62, axiom, (![A]: (~v1_xboole_0(A) => (![B]: ((~v1_xboole_0(B) & v1_zfmisc_1(B)) => (r1_tarski(A, B) => (A = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tex_2)).
% 2.23/1.30  tff(c_94, plain, (![A_36, B_37]: (r1_tarski(A_36, B_37) | k4_xboole_0(A_36, B_37)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.23/1.30  tff(c_26, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.23/1.30  tff(c_102, plain, (k4_xboole_0('#skF_1', '#skF_2')!=k1_xboole_0), inference(resolution, [status(thm)], [c_94, c_26])).
% 2.23/1.30  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.23/1.30  tff(c_115, plain, (![A_40, C_41, B_42]: (r1_tarski(A_40, C_41) | ~r1_tarski(k2_xboole_0(A_40, B_42), C_41))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.23/1.30  tff(c_126, plain, (![A_43, B_44]: (r1_tarski(A_43, k2_xboole_0(A_43, B_44)))), inference(resolution, [status(thm)], [c_6, c_115])).
% 2.23/1.30  tff(c_10, plain, (![A_3, B_4]: (k4_xboole_0(A_3, B_4)=k1_xboole_0 | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.23/1.30  tff(c_135, plain, (![A_43, B_44]: (k4_xboole_0(A_43, k2_xboole_0(A_43, B_44))=k1_xboole_0)), inference(resolution, [status(thm)], [c_126, c_10])).
% 2.23/1.30  tff(c_18, plain, (![A_12, B_13]: (k3_xboole_0(A_12, k2_xboole_0(A_12, B_13))=A_12)), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.23/1.30  tff(c_103, plain, (![A_38, B_39]: (k5_xboole_0(A_38, k3_xboole_0(A_38, B_39))=k4_xboole_0(A_38, B_39))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.23/1.30  tff(c_112, plain, (![A_12, B_13]: (k4_xboole_0(A_12, k2_xboole_0(A_12, B_13))=k5_xboole_0(A_12, A_12))), inference(superposition, [status(thm), theory('equality')], [c_18, c_103])).
% 2.23/1.30  tff(c_172, plain, (![A_12]: (k5_xboole_0(A_12, A_12)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_135, c_112])).
% 2.23/1.30  tff(c_16, plain, (![A_10, B_11]: (r1_tarski(k3_xboole_0(A_10, B_11), A_10))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.23/1.30  tff(c_67, plain, (![A_31, B_32]: (k4_xboole_0(A_31, B_32)=k1_xboole_0 | ~r1_tarski(A_31, B_32))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.23/1.30  tff(c_74, plain, (![A_10, B_11]: (k4_xboole_0(k3_xboole_0(A_10, B_11), A_10)=k1_xboole_0)), inference(resolution, [status(thm)], [c_16, c_67])).
% 2.23/1.30  tff(c_32, plain, (~v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.23/1.30  tff(c_30, plain, (v1_zfmisc_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.23/1.30  tff(c_8, plain, (![A_3, B_4]: (r1_tarski(A_3, B_4) | k4_xboole_0(A_3, B_4)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.23/1.30  tff(c_240, plain, (![B_63, A_64]: (B_63=A_64 | ~r1_tarski(A_64, B_63) | ~v1_zfmisc_1(B_63) | v1_xboole_0(B_63) | v1_xboole_0(A_64))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.23/1.30  tff(c_313, plain, (![B_77, A_78]: (B_77=A_78 | ~v1_zfmisc_1(B_77) | v1_xboole_0(B_77) | v1_xboole_0(A_78) | k4_xboole_0(A_78, B_77)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_240])).
% 2.23/1.30  tff(c_315, plain, (![A_78]: (A_78='#skF_1' | v1_xboole_0('#skF_1') | v1_xboole_0(A_78) | k4_xboole_0(A_78, '#skF_1')!=k1_xboole_0)), inference(resolution, [status(thm)], [c_30, c_313])).
% 2.23/1.30  tff(c_319, plain, (![A_79]: (A_79='#skF_1' | v1_xboole_0(A_79) | k4_xboole_0(A_79, '#skF_1')!=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_32, c_315])).
% 2.23/1.30  tff(c_28, plain, (~v1_xboole_0(k3_xboole_0('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.23/1.30  tff(c_322, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_1' | k4_xboole_0(k3_xboole_0('#skF_1', '#skF_2'), '#skF_1')!=k1_xboole_0), inference(resolution, [status(thm)], [c_319, c_28])).
% 2.23/1.30  tff(c_328, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_74, c_322])).
% 2.23/1.30  tff(c_12, plain, (![A_5, B_6]: (k5_xboole_0(A_5, k3_xboole_0(A_5, B_6))=k4_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.23/1.30  tff(c_343, plain, (k5_xboole_0('#skF_1', '#skF_1')=k4_xboole_0('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_328, c_12])).
% 2.23/1.30  tff(c_356, plain, (k4_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_172, c_343])).
% 2.23/1.30  tff(c_358, plain, $false, inference(negUnitSimplification, [status(thm)], [c_102, c_356])).
% 2.23/1.30  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.23/1.30  
% 2.23/1.30  Inference rules
% 2.23/1.30  ----------------------
% 2.23/1.30  #Ref     : 0
% 2.23/1.30  #Sup     : 72
% 2.23/1.30  #Fact    : 0
% 2.23/1.30  #Define  : 0
% 2.23/1.30  #Split   : 0
% 2.23/1.30  #Chain   : 0
% 2.23/1.30  #Close   : 0
% 2.23/1.30  
% 2.23/1.30  Ordering : KBO
% 2.23/1.30  
% 2.23/1.30  Simplification rules
% 2.23/1.30  ----------------------
% 2.23/1.30  #Subsume      : 5
% 2.23/1.30  #Demod        : 22
% 2.23/1.30  #Tautology    : 35
% 2.23/1.30  #SimpNegUnit  : 2
% 2.23/1.30  #BackRed      : 1
% 2.23/1.30  
% 2.23/1.30  #Partial instantiations: 0
% 2.23/1.30  #Strategies tried      : 1
% 2.23/1.30  
% 2.23/1.30  Timing (in seconds)
% 2.23/1.30  ----------------------
% 2.23/1.30  Preprocessing        : 0.32
% 2.23/1.30  Parsing              : 0.17
% 2.23/1.30  CNF conversion       : 0.02
% 2.23/1.30  Main loop            : 0.21
% 2.23/1.30  Inferencing          : 0.09
% 2.23/1.30  Reduction            : 0.06
% 2.23/1.30  Demodulation         : 0.05
% 2.23/1.30  BG Simplification    : 0.01
% 2.23/1.30  Subsumption          : 0.04
% 2.23/1.30  Abstraction          : 0.02
% 2.23/1.30  MUC search           : 0.00
% 2.23/1.30  Cooper               : 0.00
% 2.23/1.30  Total                : 0.56
% 2.23/1.30  Index Insertion      : 0.00
% 2.23/1.30  Index Deletion       : 0.00
% 2.23/1.30  Index Matching       : 0.00
% 2.23/1.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
