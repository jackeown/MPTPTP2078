%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:05 EST 2020

% Result     : Theorem 2.55s
% Output     : CNFRefutation 2.55s
% Verified   : 
% Statistics : Number of formulae       :   54 ( 104 expanded)
%              Number of leaves         :   22 (  44 expanded)
%              Depth                    :    9
%              Number of atoms          :  101 ( 226 expanded)
%              Number of equality atoms :    8 (  15 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_xboole_0 > r2_hidden > r1_tarski > v3_ordinal1 > v2_ordinal1 > v1_ordinal1 > #nlpp > k3_tarski > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(v1_ordinal1,type,(
    v1_ordinal1: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v3_ordinal1,type,(
    v3_ordinal1: $i > $o )).

tff(v2_ordinal1,type,(
    v2_ordinal1: $i > $o )).

tff(r2_xboole_0,type,(
    r2_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_82,negated_conjecture,(
    ~ ! [A] :
        ( v3_ordinal1(A)
       => v3_ordinal1(k3_tarski(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_ordinal1)).

tff(f_55,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ( v1_ordinal1(A)
        & v2_ordinal1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_ordinal1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
         => r1_tarski(C,B) )
     => r1_tarski(k3_tarski(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_zfmisc_1)).

tff(f_62,axiom,(
    ! [A] :
      ( v1_ordinal1(A)
    <=> ! [B] :
          ( r2_hidden(B,A)
         => r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_ordinal1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => r1_tarski(k3_tarski(A),k3_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_zfmisc_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(k3_tarski(A),B)
        & r2_hidden(C,A) )
     => r1_tarski(C,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_setfam_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        & A != B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).

tff(f_71,axiom,(
    ! [A] :
      ( v1_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ( r2_xboole_0(A,B)
           => r2_hidden(A,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_ordinal1)).

tff(f_77,axiom,(
    ! [A,B] :
      ( v3_ordinal1(B)
     => ( r2_hidden(A,B)
       => v3_ordinal1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_ordinal1)).

tff(c_32,plain,(
    v3_ordinal1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_34,plain,(
    ! [A_22] :
      ( v1_ordinal1(A_22)
      | ~ v3_ordinal1(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_38,plain,(
    v1_ordinal1('#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_34])).

tff(c_69,plain,(
    ! [A_36,B_37] :
      ( r2_hidden('#skF_1'(A_36,B_37),A_36)
      | r1_tarski(k3_tarski(A_36),B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_20,plain,(
    ! [B_15,A_12] :
      ( r1_tarski(B_15,A_12)
      | ~ r2_hidden(B_15,A_12)
      | ~ v1_ordinal1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_145,plain,(
    ! [A_55,B_56] :
      ( r1_tarski('#skF_1'(A_55,B_56),A_55)
      | ~ v1_ordinal1(A_55)
      | r1_tarski(k3_tarski(A_55),B_56) ) ),
    inference(resolution,[status(thm)],[c_69,c_20])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( ~ r1_tarski('#skF_1'(A_3,B_4),B_4)
      | r1_tarski(k3_tarski(A_3),B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_167,plain,(
    ! [A_57] :
      ( ~ v1_ordinal1(A_57)
      | r1_tarski(k3_tarski(A_57),A_57) ) ),
    inference(resolution,[status(thm)],[c_145,c_8])).

tff(c_12,plain,(
    ! [A_6,B_7] :
      ( r1_tarski(k3_tarski(A_6),k3_tarski(B_7))
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_24,plain,(
    ! [A_12] :
      ( r2_hidden('#skF_2'(A_12),A_12)
      | v1_ordinal1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_79,plain,(
    ! [C_40,B_41,A_42] :
      ( r1_tarski(C_40,B_41)
      | ~ r2_hidden(C_40,A_42)
      | ~ r1_tarski(k3_tarski(A_42),B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_91,plain,(
    ! [A_45,B_46] :
      ( r1_tarski('#skF_2'(A_45),B_46)
      | ~ r1_tarski(k3_tarski(A_45),B_46)
      | v1_ordinal1(A_45) ) ),
    inference(resolution,[status(thm)],[c_24,c_79])).

tff(c_101,plain,(
    ! [A_49,B_50] :
      ( r1_tarski('#skF_2'(A_49),k3_tarski(B_50))
      | v1_ordinal1(A_49)
      | ~ r1_tarski(A_49,B_50) ) ),
    inference(resolution,[status(thm)],[c_12,c_91])).

tff(c_22,plain,(
    ! [A_12] :
      ( ~ r1_tarski('#skF_2'(A_12),A_12)
      | v1_ordinal1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_106,plain,(
    ! [B_50] :
      ( v1_ordinal1(k3_tarski(B_50))
      | ~ r1_tarski(k3_tarski(B_50),B_50) ) ),
    inference(resolution,[status(thm)],[c_101,c_22])).

tff(c_180,plain,(
    ! [A_57] :
      ( v1_ordinal1(k3_tarski(A_57))
      | ~ v1_ordinal1(A_57) ) ),
    inference(resolution,[status(thm)],[c_167,c_106])).

tff(c_162,plain,(
    ! [A_55] :
      ( ~ v1_ordinal1(A_55)
      | r1_tarski(k3_tarski(A_55),A_55) ) ),
    inference(resolution,[status(thm)],[c_145,c_8])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r2_xboole_0(A_1,B_2)
      | B_2 = A_1
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_86,plain,(
    ! [A_43,B_44] :
      ( r2_hidden(A_43,B_44)
      | ~ r2_xboole_0(A_43,B_44)
      | ~ v3_ordinal1(B_44)
      | ~ v1_ordinal1(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_212,plain,(
    ! [A_65,B_66] :
      ( r2_hidden(A_65,B_66)
      | ~ v3_ordinal1(B_66)
      | ~ v1_ordinal1(A_65)
      | B_66 = A_65
      | ~ r1_tarski(A_65,B_66) ) ),
    inference(resolution,[status(thm)],[c_2,c_86])).

tff(c_28,plain,(
    ! [A_19,B_20] :
      ( v3_ordinal1(A_19)
      | ~ r2_hidden(A_19,B_20)
      | ~ v3_ordinal1(B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_227,plain,(
    ! [A_70,B_71] :
      ( v3_ordinal1(A_70)
      | ~ v3_ordinal1(B_71)
      | ~ v1_ordinal1(A_70)
      | B_71 = A_70
      | ~ r1_tarski(A_70,B_71) ) ),
    inference(resolution,[status(thm)],[c_212,c_28])).

tff(c_330,plain,(
    ! [A_88] :
      ( v3_ordinal1(k3_tarski(A_88))
      | ~ v3_ordinal1(A_88)
      | ~ v1_ordinal1(k3_tarski(A_88))
      | k3_tarski(A_88) = A_88
      | ~ v1_ordinal1(A_88) ) ),
    inference(resolution,[status(thm)],[c_162,c_227])).

tff(c_30,plain,(
    ~ v3_ordinal1(k3_tarski('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_339,plain,
    ( ~ v3_ordinal1('#skF_3')
    | ~ v1_ordinal1(k3_tarski('#skF_3'))
    | k3_tarski('#skF_3') = '#skF_3'
    | ~ v1_ordinal1('#skF_3') ),
    inference(resolution,[status(thm)],[c_330,c_30])).

tff(c_344,plain,
    ( ~ v1_ordinal1(k3_tarski('#skF_3'))
    | k3_tarski('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_32,c_339])).

tff(c_390,plain,(
    ~ v1_ordinal1(k3_tarski('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_344])).

tff(c_396,plain,(
    ~ v1_ordinal1('#skF_3') ),
    inference(resolution,[status(thm)],[c_180,c_390])).

tff(c_403,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_396])).

tff(c_404,plain,(
    k3_tarski('#skF_3') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_344])).

tff(c_406,plain,(
    ~ v3_ordinal1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_404,c_30])).

tff(c_409,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_406])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n022.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 19:59:25 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.55/1.42  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.55/1.42  
% 2.55/1.42  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.55/1.43  %$ r2_xboole_0 > r2_hidden > r1_tarski > v3_ordinal1 > v2_ordinal1 > v1_ordinal1 > #nlpp > k3_tarski > #skF_2 > #skF_3 > #skF_1
% 2.55/1.43  
% 2.55/1.43  %Foreground sorts:
% 2.55/1.43  
% 2.55/1.43  
% 2.55/1.43  %Background operators:
% 2.55/1.43  
% 2.55/1.43  
% 2.55/1.43  %Foreground operators:
% 2.55/1.43  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.55/1.43  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.55/1.43  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.55/1.43  tff(v1_ordinal1, type, v1_ordinal1: $i > $o).
% 2.55/1.43  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.55/1.43  tff('#skF_3', type, '#skF_3': $i).
% 2.55/1.43  tff(v3_ordinal1, type, v3_ordinal1: $i > $o).
% 2.55/1.43  tff(v2_ordinal1, type, v2_ordinal1: $i > $o).
% 2.55/1.43  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 2.55/1.43  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.55/1.43  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.55/1.43  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.55/1.43  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.55/1.43  
% 2.55/1.44  tff(f_82, negated_conjecture, ~(![A]: (v3_ordinal1(A) => v3_ordinal1(k3_tarski(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t30_ordinal1)).
% 2.55/1.44  tff(f_55, axiom, (![A]: (v3_ordinal1(A) => (v1_ordinal1(A) & v2_ordinal1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_ordinal1)).
% 2.55/1.44  tff(f_39, axiom, (![A, B]: ((![C]: (r2_hidden(C, A) => r1_tarski(C, B))) => r1_tarski(k3_tarski(A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_zfmisc_1)).
% 2.55/1.44  tff(f_62, axiom, (![A]: (v1_ordinal1(A) <=> (![B]: (r2_hidden(B, A) => r1_tarski(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_ordinal1)).
% 2.55/1.44  tff(f_43, axiom, (![A, B]: (r1_tarski(A, B) => r1_tarski(k3_tarski(A), k3_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_zfmisc_1)).
% 2.55/1.44  tff(f_49, axiom, (![A, B, C]: ((r1_tarski(k3_tarski(A), B) & r2_hidden(C, A)) => r1_tarski(C, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t56_setfam_1)).
% 2.55/1.44  tff(f_32, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_xboole_0)).
% 2.55/1.44  tff(f_71, axiom, (![A]: (v1_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r2_xboole_0(A, B) => r2_hidden(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_ordinal1)).
% 2.55/1.44  tff(f_77, axiom, (![A, B]: (v3_ordinal1(B) => (r2_hidden(A, B) => v3_ordinal1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_ordinal1)).
% 2.55/1.44  tff(c_32, plain, (v3_ordinal1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.55/1.44  tff(c_34, plain, (![A_22]: (v1_ordinal1(A_22) | ~v3_ordinal1(A_22))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.55/1.44  tff(c_38, plain, (v1_ordinal1('#skF_3')), inference(resolution, [status(thm)], [c_32, c_34])).
% 2.55/1.44  tff(c_69, plain, (![A_36, B_37]: (r2_hidden('#skF_1'(A_36, B_37), A_36) | r1_tarski(k3_tarski(A_36), B_37))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.55/1.44  tff(c_20, plain, (![B_15, A_12]: (r1_tarski(B_15, A_12) | ~r2_hidden(B_15, A_12) | ~v1_ordinal1(A_12))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.55/1.44  tff(c_145, plain, (![A_55, B_56]: (r1_tarski('#skF_1'(A_55, B_56), A_55) | ~v1_ordinal1(A_55) | r1_tarski(k3_tarski(A_55), B_56))), inference(resolution, [status(thm)], [c_69, c_20])).
% 2.55/1.44  tff(c_8, plain, (![A_3, B_4]: (~r1_tarski('#skF_1'(A_3, B_4), B_4) | r1_tarski(k3_tarski(A_3), B_4))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.55/1.44  tff(c_167, plain, (![A_57]: (~v1_ordinal1(A_57) | r1_tarski(k3_tarski(A_57), A_57))), inference(resolution, [status(thm)], [c_145, c_8])).
% 2.55/1.44  tff(c_12, plain, (![A_6, B_7]: (r1_tarski(k3_tarski(A_6), k3_tarski(B_7)) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.55/1.44  tff(c_24, plain, (![A_12]: (r2_hidden('#skF_2'(A_12), A_12) | v1_ordinal1(A_12))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.55/1.44  tff(c_79, plain, (![C_40, B_41, A_42]: (r1_tarski(C_40, B_41) | ~r2_hidden(C_40, A_42) | ~r1_tarski(k3_tarski(A_42), B_41))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.55/1.44  tff(c_91, plain, (![A_45, B_46]: (r1_tarski('#skF_2'(A_45), B_46) | ~r1_tarski(k3_tarski(A_45), B_46) | v1_ordinal1(A_45))), inference(resolution, [status(thm)], [c_24, c_79])).
% 2.55/1.44  tff(c_101, plain, (![A_49, B_50]: (r1_tarski('#skF_2'(A_49), k3_tarski(B_50)) | v1_ordinal1(A_49) | ~r1_tarski(A_49, B_50))), inference(resolution, [status(thm)], [c_12, c_91])).
% 2.55/1.44  tff(c_22, plain, (![A_12]: (~r1_tarski('#skF_2'(A_12), A_12) | v1_ordinal1(A_12))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.55/1.44  tff(c_106, plain, (![B_50]: (v1_ordinal1(k3_tarski(B_50)) | ~r1_tarski(k3_tarski(B_50), B_50))), inference(resolution, [status(thm)], [c_101, c_22])).
% 2.55/1.44  tff(c_180, plain, (![A_57]: (v1_ordinal1(k3_tarski(A_57)) | ~v1_ordinal1(A_57))), inference(resolution, [status(thm)], [c_167, c_106])).
% 2.55/1.44  tff(c_162, plain, (![A_55]: (~v1_ordinal1(A_55) | r1_tarski(k3_tarski(A_55), A_55))), inference(resolution, [status(thm)], [c_145, c_8])).
% 2.55/1.44  tff(c_2, plain, (![A_1, B_2]: (r2_xboole_0(A_1, B_2) | B_2=A_1 | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.55/1.44  tff(c_86, plain, (![A_43, B_44]: (r2_hidden(A_43, B_44) | ~r2_xboole_0(A_43, B_44) | ~v3_ordinal1(B_44) | ~v1_ordinal1(A_43))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.55/1.44  tff(c_212, plain, (![A_65, B_66]: (r2_hidden(A_65, B_66) | ~v3_ordinal1(B_66) | ~v1_ordinal1(A_65) | B_66=A_65 | ~r1_tarski(A_65, B_66))), inference(resolution, [status(thm)], [c_2, c_86])).
% 2.55/1.44  tff(c_28, plain, (![A_19, B_20]: (v3_ordinal1(A_19) | ~r2_hidden(A_19, B_20) | ~v3_ordinal1(B_20))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.55/1.44  tff(c_227, plain, (![A_70, B_71]: (v3_ordinal1(A_70) | ~v3_ordinal1(B_71) | ~v1_ordinal1(A_70) | B_71=A_70 | ~r1_tarski(A_70, B_71))), inference(resolution, [status(thm)], [c_212, c_28])).
% 2.55/1.44  tff(c_330, plain, (![A_88]: (v3_ordinal1(k3_tarski(A_88)) | ~v3_ordinal1(A_88) | ~v1_ordinal1(k3_tarski(A_88)) | k3_tarski(A_88)=A_88 | ~v1_ordinal1(A_88))), inference(resolution, [status(thm)], [c_162, c_227])).
% 2.55/1.44  tff(c_30, plain, (~v3_ordinal1(k3_tarski('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.55/1.44  tff(c_339, plain, (~v3_ordinal1('#skF_3') | ~v1_ordinal1(k3_tarski('#skF_3')) | k3_tarski('#skF_3')='#skF_3' | ~v1_ordinal1('#skF_3')), inference(resolution, [status(thm)], [c_330, c_30])).
% 2.55/1.44  tff(c_344, plain, (~v1_ordinal1(k3_tarski('#skF_3')) | k3_tarski('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_38, c_32, c_339])).
% 2.55/1.44  tff(c_390, plain, (~v1_ordinal1(k3_tarski('#skF_3'))), inference(splitLeft, [status(thm)], [c_344])).
% 2.55/1.44  tff(c_396, plain, (~v1_ordinal1('#skF_3')), inference(resolution, [status(thm)], [c_180, c_390])).
% 2.55/1.44  tff(c_403, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_396])).
% 2.55/1.44  tff(c_404, plain, (k3_tarski('#skF_3')='#skF_3'), inference(splitRight, [status(thm)], [c_344])).
% 2.55/1.44  tff(c_406, plain, (~v3_ordinal1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_404, c_30])).
% 2.55/1.44  tff(c_409, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_406])).
% 2.55/1.44  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.55/1.44  
% 2.55/1.44  Inference rules
% 2.55/1.44  ----------------------
% 2.55/1.44  #Ref     : 0
% 2.55/1.44  #Sup     : 80
% 2.55/1.44  #Fact    : 0
% 2.55/1.44  #Define  : 0
% 2.55/1.44  #Split   : 1
% 2.55/1.44  #Chain   : 0
% 2.55/1.44  #Close   : 0
% 2.55/1.44  
% 2.55/1.44  Ordering : KBO
% 2.55/1.44  
% 2.55/1.44  Simplification rules
% 2.55/1.44  ----------------------
% 2.55/1.44  #Subsume      : 12
% 2.55/1.44  #Demod        : 6
% 2.55/1.44  #Tautology    : 6
% 2.55/1.44  #SimpNegUnit  : 0
% 2.55/1.44  #BackRed      : 1
% 2.55/1.44  
% 2.55/1.44  #Partial instantiations: 0
% 2.55/1.44  #Strategies tried      : 1
% 2.55/1.44  
% 2.55/1.44  Timing (in seconds)
% 2.55/1.44  ----------------------
% 2.55/1.44  Preprocessing        : 0.29
% 2.55/1.44  Parsing              : 0.17
% 2.55/1.44  CNF conversion       : 0.02
% 2.55/1.44  Main loop            : 0.33
% 2.55/1.44  Inferencing          : 0.14
% 2.55/1.44  Reduction            : 0.07
% 2.55/1.44  Demodulation         : 0.04
% 2.55/1.44  BG Simplification    : 0.02
% 2.55/1.44  Subsumption          : 0.09
% 2.55/1.44  Abstraction          : 0.01
% 2.55/1.44  MUC search           : 0.00
% 2.55/1.44  Cooper               : 0.00
% 2.55/1.44  Total                : 0.65
% 2.55/1.44  Index Insertion      : 0.00
% 2.55/1.44  Index Deletion       : 0.00
% 2.55/1.44  Index Matching       : 0.00
% 2.55/1.44  BG Taut test         : 0.00
%------------------------------------------------------------------------------
