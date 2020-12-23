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
% DateTime   : Thu Dec  3 10:28:27 EST 2020

% Result     : Theorem 2.47s
% Output     : CNFRefutation 2.79s
% Verified   : 
% Statistics : Number of formulae       :   51 (  61 expanded)
%              Number of leaves         :   21 (  30 expanded)
%              Depth                    :    7
%              Number of atoms          :   72 (  95 expanded)
%              Number of equality atoms :   33 (  38 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > v1_zfmisc_1 > v1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_35,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_68,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v1_xboole_0(A)
          & v1_zfmisc_1(A) )
       => ! [B] :
            ( ~ v1_xboole_0(k3_xboole_0(A,B))
           => r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tex_2)).

tff(f_56,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & v1_zfmisc_1(B) )
         => ( r1_tarski(A,B)
           => A = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tex_2)).

tff(c_8,plain,(
    ! [A_5,B_6] : r1_tarski(k4_xboole_0(A_5,B_6),A_5) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_29,plain,(
    ! [A_21,B_22] :
      ( k4_xboole_0(A_21,B_22) = k1_xboole_0
      | ~ r1_tarski(A_21,B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_33,plain,(
    ! [A_5,B_6] : k4_xboole_0(k4_xboole_0(A_5,B_6),A_5) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8,c_29])).

tff(c_10,plain,(
    ! [A_7,B_8] : k4_xboole_0(A_7,k4_xboole_0(A_7,B_8)) = k3_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_118,plain,(
    ! [A_33,B_34] :
      ( r1_xboole_0(A_33,B_34)
      | k4_xboole_0(A_33,B_34) != A_33 ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( r1_xboole_0(B_2,A_1)
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_290,plain,(
    ! [B_50,A_51] :
      ( r1_xboole_0(B_50,A_51)
      | k4_xboole_0(A_51,B_50) != A_51 ) ),
    inference(resolution,[status(thm)],[c_118,c_2])).

tff(c_12,plain,(
    ! [A_9,B_10] :
      ( k4_xboole_0(A_9,B_10) = A_9
      | ~ r1_xboole_0(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_298,plain,(
    ! [B_52,A_53] :
      ( k4_xboole_0(B_52,A_53) = B_52
      | k4_xboole_0(A_53,B_52) != A_53 ) ),
    inference(resolution,[status(thm)],[c_290,c_12])).

tff(c_304,plain,(
    ! [A_7,B_8] :
      ( k4_xboole_0(k4_xboole_0(A_7,B_8),A_7) = k4_xboole_0(A_7,B_8)
      | k3_xboole_0(A_7,B_8) != A_7 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_298])).

tff(c_317,plain,(
    ! [A_54,B_55] :
      ( k4_xboole_0(A_54,B_55) = k1_xboole_0
      | k3_xboole_0(A_54,B_55) != A_54 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_33,c_304])).

tff(c_126,plain,(
    ! [A_35,B_36] :
      ( r1_tarski(A_35,B_36)
      | k4_xboole_0(A_35,B_36) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_20,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_134,plain,(
    k4_xboole_0('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_126,c_20])).

tff(c_386,plain,(
    k3_xboole_0('#skF_1','#skF_2') != '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_317,c_134])).

tff(c_135,plain,(
    ! [A_37,B_38] : k4_xboole_0(A_37,k4_xboole_0(A_37,B_38)) = k3_xboole_0(A_37,B_38) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_188,plain,(
    ! [A_40,B_41] : r1_tarski(k3_xboole_0(A_40,B_41),A_40) ),
    inference(superposition,[status(thm),theory(equality)],[c_135,c_8])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( k4_xboole_0(A_3,B_4) = k1_xboole_0
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_195,plain,(
    ! [A_40,B_41] : k4_xboole_0(k3_xboole_0(A_40,B_41),A_40) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_188,c_6])).

tff(c_26,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_24,plain,(
    v1_zfmisc_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( r1_tarski(A_3,B_4)
      | k4_xboole_0(A_3,B_4) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_205,plain,(
    ! [B_44,A_45] :
      ( B_44 = A_45
      | ~ r1_tarski(A_45,B_44)
      | ~ v1_zfmisc_1(B_44)
      | v1_xboole_0(B_44)
      | v1_xboole_0(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_1109,plain,(
    ! [B_79,A_80] :
      ( B_79 = A_80
      | ~ v1_zfmisc_1(B_79)
      | v1_xboole_0(B_79)
      | v1_xboole_0(A_80)
      | k4_xboole_0(A_80,B_79) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_205])).

tff(c_1111,plain,(
    ! [A_80] :
      ( A_80 = '#skF_1'
      | v1_xboole_0('#skF_1')
      | v1_xboole_0(A_80)
      | k4_xboole_0(A_80,'#skF_1') != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_24,c_1109])).

tff(c_1115,plain,(
    ! [A_81] :
      ( A_81 = '#skF_1'
      | v1_xboole_0(A_81)
      | k4_xboole_0(A_81,'#skF_1') != k1_xboole_0 ) ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_1111])).

tff(c_22,plain,(
    ~ v1_xboole_0(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_1118,plain,
    ( k3_xboole_0('#skF_1','#skF_2') = '#skF_1'
    | k4_xboole_0(k3_xboole_0('#skF_1','#skF_2'),'#skF_1') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1115,c_22])).

tff(c_1124,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_195,c_1118])).

tff(c_1126,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_386,c_1124])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:02:15 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.47/1.45  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.47/1.45  
% 2.47/1.45  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.47/1.46  %$ r1_xboole_0 > r1_tarski > v1_zfmisc_1 > v1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1
% 2.47/1.46  
% 2.47/1.46  %Foreground sorts:
% 2.47/1.46  
% 2.47/1.46  
% 2.47/1.46  %Background operators:
% 2.47/1.46  
% 2.47/1.46  
% 2.47/1.46  %Foreground operators:
% 2.47/1.46  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.47/1.46  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.47/1.46  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.47/1.46  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.47/1.46  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.47/1.46  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.47/1.46  tff('#skF_2', type, '#skF_2': $i).
% 2.47/1.46  tff('#skF_1', type, '#skF_1': $i).
% 2.47/1.46  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.47/1.46  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.47/1.46  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 2.47/1.46  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.47/1.46  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.47/1.46  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.47/1.46  
% 2.79/1.47  tff(f_35, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 2.79/1.47  tff(f_33, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.79/1.47  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.79/1.47  tff(f_41, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 2.79/1.47  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 2.79/1.47  tff(f_68, negated_conjecture, ~(![A]: ((~v1_xboole_0(A) & v1_zfmisc_1(A)) => (![B]: (~v1_xboole_0(k3_xboole_0(A, B)) => r1_tarski(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tex_2)).
% 2.79/1.47  tff(f_56, axiom, (![A]: (~v1_xboole_0(A) => (![B]: ((~v1_xboole_0(B) & v1_zfmisc_1(B)) => (r1_tarski(A, B) => (A = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tex_2)).
% 2.79/1.47  tff(c_8, plain, (![A_5, B_6]: (r1_tarski(k4_xboole_0(A_5, B_6), A_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.79/1.47  tff(c_29, plain, (![A_21, B_22]: (k4_xboole_0(A_21, B_22)=k1_xboole_0 | ~r1_tarski(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.79/1.47  tff(c_33, plain, (![A_5, B_6]: (k4_xboole_0(k4_xboole_0(A_5, B_6), A_5)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_29])).
% 2.79/1.47  tff(c_10, plain, (![A_7, B_8]: (k4_xboole_0(A_7, k4_xboole_0(A_7, B_8))=k3_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.79/1.47  tff(c_118, plain, (![A_33, B_34]: (r1_xboole_0(A_33, B_34) | k4_xboole_0(A_33, B_34)!=A_33)), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.79/1.47  tff(c_2, plain, (![B_2, A_1]: (r1_xboole_0(B_2, A_1) | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.79/1.47  tff(c_290, plain, (![B_50, A_51]: (r1_xboole_0(B_50, A_51) | k4_xboole_0(A_51, B_50)!=A_51)), inference(resolution, [status(thm)], [c_118, c_2])).
% 2.79/1.47  tff(c_12, plain, (![A_9, B_10]: (k4_xboole_0(A_9, B_10)=A_9 | ~r1_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.79/1.47  tff(c_298, plain, (![B_52, A_53]: (k4_xboole_0(B_52, A_53)=B_52 | k4_xboole_0(A_53, B_52)!=A_53)), inference(resolution, [status(thm)], [c_290, c_12])).
% 2.79/1.47  tff(c_304, plain, (![A_7, B_8]: (k4_xboole_0(k4_xboole_0(A_7, B_8), A_7)=k4_xboole_0(A_7, B_8) | k3_xboole_0(A_7, B_8)!=A_7)), inference(superposition, [status(thm), theory('equality')], [c_10, c_298])).
% 2.79/1.47  tff(c_317, plain, (![A_54, B_55]: (k4_xboole_0(A_54, B_55)=k1_xboole_0 | k3_xboole_0(A_54, B_55)!=A_54)), inference(demodulation, [status(thm), theory('equality')], [c_33, c_304])).
% 2.79/1.47  tff(c_126, plain, (![A_35, B_36]: (r1_tarski(A_35, B_36) | k4_xboole_0(A_35, B_36)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.79/1.47  tff(c_20, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.79/1.47  tff(c_134, plain, (k4_xboole_0('#skF_1', '#skF_2')!=k1_xboole_0), inference(resolution, [status(thm)], [c_126, c_20])).
% 2.79/1.47  tff(c_386, plain, (k3_xboole_0('#skF_1', '#skF_2')!='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_317, c_134])).
% 2.79/1.47  tff(c_135, plain, (![A_37, B_38]: (k4_xboole_0(A_37, k4_xboole_0(A_37, B_38))=k3_xboole_0(A_37, B_38))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.79/1.47  tff(c_188, plain, (![A_40, B_41]: (r1_tarski(k3_xboole_0(A_40, B_41), A_40))), inference(superposition, [status(thm), theory('equality')], [c_135, c_8])).
% 2.79/1.47  tff(c_6, plain, (![A_3, B_4]: (k4_xboole_0(A_3, B_4)=k1_xboole_0 | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.79/1.47  tff(c_195, plain, (![A_40, B_41]: (k4_xboole_0(k3_xboole_0(A_40, B_41), A_40)=k1_xboole_0)), inference(resolution, [status(thm)], [c_188, c_6])).
% 2.79/1.47  tff(c_26, plain, (~v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.79/1.47  tff(c_24, plain, (v1_zfmisc_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.79/1.47  tff(c_4, plain, (![A_3, B_4]: (r1_tarski(A_3, B_4) | k4_xboole_0(A_3, B_4)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.79/1.47  tff(c_205, plain, (![B_44, A_45]: (B_44=A_45 | ~r1_tarski(A_45, B_44) | ~v1_zfmisc_1(B_44) | v1_xboole_0(B_44) | v1_xboole_0(A_45))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.79/1.47  tff(c_1109, plain, (![B_79, A_80]: (B_79=A_80 | ~v1_zfmisc_1(B_79) | v1_xboole_0(B_79) | v1_xboole_0(A_80) | k4_xboole_0(A_80, B_79)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_205])).
% 2.79/1.47  tff(c_1111, plain, (![A_80]: (A_80='#skF_1' | v1_xboole_0('#skF_1') | v1_xboole_0(A_80) | k4_xboole_0(A_80, '#skF_1')!=k1_xboole_0)), inference(resolution, [status(thm)], [c_24, c_1109])).
% 2.79/1.47  tff(c_1115, plain, (![A_81]: (A_81='#skF_1' | v1_xboole_0(A_81) | k4_xboole_0(A_81, '#skF_1')!=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_26, c_1111])).
% 2.79/1.47  tff(c_22, plain, (~v1_xboole_0(k3_xboole_0('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.79/1.47  tff(c_1118, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_1' | k4_xboole_0(k3_xboole_0('#skF_1', '#skF_2'), '#skF_1')!=k1_xboole_0), inference(resolution, [status(thm)], [c_1115, c_22])).
% 2.79/1.47  tff(c_1124, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_195, c_1118])).
% 2.79/1.47  tff(c_1126, plain, $false, inference(negUnitSimplification, [status(thm)], [c_386, c_1124])).
% 2.79/1.47  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.79/1.47  
% 2.79/1.47  Inference rules
% 2.79/1.47  ----------------------
% 2.79/1.47  #Ref     : 0
% 2.79/1.47  #Sup     : 267
% 2.79/1.47  #Fact    : 0
% 2.79/1.47  #Define  : 0
% 2.79/1.47  #Split   : 0
% 2.79/1.47  #Chain   : 0
% 2.79/1.47  #Close   : 0
% 2.79/1.47  
% 2.79/1.47  Ordering : KBO
% 2.79/1.47  
% 2.79/1.47  Simplification rules
% 2.79/1.47  ----------------------
% 2.79/1.47  #Subsume      : 3
% 2.79/1.47  #Demod        : 207
% 2.79/1.47  #Tautology    : 209
% 2.79/1.47  #SimpNegUnit  : 2
% 2.79/1.47  #BackRed      : 0
% 2.79/1.47  
% 2.79/1.47  #Partial instantiations: 0
% 2.79/1.47  #Strategies tried      : 1
% 2.79/1.47  
% 2.79/1.47  Timing (in seconds)
% 2.79/1.47  ----------------------
% 2.82/1.47  Preprocessing        : 0.30
% 2.82/1.47  Parsing              : 0.17
% 2.82/1.47  CNF conversion       : 0.02
% 2.82/1.47  Main loop            : 0.34
% 2.82/1.47  Inferencing          : 0.14
% 2.82/1.47  Reduction            : 0.11
% 2.82/1.47  Demodulation         : 0.08
% 2.82/1.47  BG Simplification    : 0.02
% 2.82/1.47  Subsumption          : 0.05
% 2.82/1.47  Abstraction          : 0.02
% 2.82/1.47  MUC search           : 0.00
% 2.82/1.47  Cooper               : 0.00
% 2.82/1.47  Total                : 0.67
% 2.82/1.47  Index Insertion      : 0.00
% 2.82/1.47  Index Deletion       : 0.00
% 2.82/1.47  Index Matching       : 0.00
% 2.82/1.47  BG Taut test         : 0.00
%------------------------------------------------------------------------------
