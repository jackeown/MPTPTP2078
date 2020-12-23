%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:26 EST 2020

% Result     : Theorem 2.92s
% Output     : CNFRefutation 3.04s
% Verified   : 
% Statistics : Number of formulae       :   55 (  70 expanded)
%              Number of leaves         :   30 (  40 expanded)
%              Depth                    :    7
%              Number of atoms          :   69 ( 110 expanded)
%              Number of equality atoms :    6 (  10 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > k6_enumset1 > k5_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_relat_1 > k2_mcart_1 > k1_relat_1 > k1_mcart_1 > #skF_1 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_74,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( r2_hidden(B,A)
           => ( r2_hidden(k1_mcart_1(B),k1_relat_1(A))
              & r2_hidden(k2_mcart_1(B),k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_mcart_1)).

tff(f_58,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k3_xboole_0(A,k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A))) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_relat_1)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k5_xboole_0(B,C))
    <=> ~ ( r2_hidden(A,B)
        <=> r2_hidden(A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_0)).

tff(f_44,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k4_xboole_0(k2_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t101_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_64,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k2_zfmisc_1(B,C))
     => ( r2_hidden(k1_mcart_1(A),B)
        & r2_hidden(k2_mcart_1(A),C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).

tff(c_54,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_52,plain,(
    r2_hidden('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_44,plain,(
    ! [A_30] :
      ( k3_xboole_0(A_30,k2_zfmisc_1(k1_relat_1(A_30),k2_relat_1(A_30))) = A_30
      | ~ v1_relat_1(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_352,plain,(
    ! [A_116,C_117,B_118] :
      ( r2_hidden(A_116,C_117)
      | ~ r2_hidden(A_116,B_118)
      | r2_hidden(A_116,k5_xboole_0(B_118,C_117)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_314,plain,(
    ! [A_104,B_105] : k4_xboole_0(k2_xboole_0(A_104,B_105),k3_xboole_0(A_104,B_105)) = k5_xboole_0(A_104,B_105) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_4,plain,(
    ! [D_6,B_2,A_1] :
      ( ~ r2_hidden(D_6,B_2)
      | ~ r2_hidden(D_6,k4_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_320,plain,(
    ! [D_6,A_104,B_105] :
      ( ~ r2_hidden(D_6,k3_xboole_0(A_104,B_105))
      | ~ r2_hidden(D_6,k5_xboole_0(A_104,B_105)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_314,c_4])).

tff(c_395,plain,(
    ! [A_131,B_132,C_133] :
      ( ~ r2_hidden(A_131,k3_xboole_0(B_132,C_133))
      | r2_hidden(A_131,C_133)
      | ~ r2_hidden(A_131,B_132) ) ),
    inference(resolution,[status(thm)],[c_352,c_320])).

tff(c_458,plain,(
    ! [A_150,A_151] :
      ( ~ r2_hidden(A_150,A_151)
      | r2_hidden(A_150,k2_zfmisc_1(k1_relat_1(A_151),k2_relat_1(A_151)))
      | ~ r2_hidden(A_150,A_151)
      | ~ v1_relat_1(A_151) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_395])).

tff(c_46,plain,(
    ! [A_31,C_33,B_32] :
      ( r2_hidden(k2_mcart_1(A_31),C_33)
      | ~ r2_hidden(A_31,k2_zfmisc_1(B_32,C_33)) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_622,plain,(
    ! [A_159,A_160] :
      ( r2_hidden(k2_mcart_1(A_159),k2_relat_1(A_160))
      | ~ r2_hidden(A_159,A_160)
      | ~ v1_relat_1(A_160) ) ),
    inference(resolution,[status(thm)],[c_458,c_46])).

tff(c_130,plain,(
    ! [A_72,C_73,B_74] :
      ( r2_hidden(A_72,C_73)
      | ~ r2_hidden(A_72,B_74)
      | r2_hidden(A_72,k5_xboole_0(B_74,C_73)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_96,plain,(
    ! [A_55,B_56] : k4_xboole_0(k2_xboole_0(A_55,B_56),k3_xboole_0(A_55,B_56)) = k5_xboole_0(A_55,B_56) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_102,plain,(
    ! [D_6,A_55,B_56] :
      ( ~ r2_hidden(D_6,k3_xboole_0(A_55,B_56))
      | ~ r2_hidden(D_6,k5_xboole_0(A_55,B_56)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_96,c_4])).

tff(c_164,plain,(
    ! [A_78,B_79,C_80] :
      ( ~ r2_hidden(A_78,k3_xboole_0(B_79,C_80))
      | r2_hidden(A_78,C_80)
      | ~ r2_hidden(A_78,B_79) ) ),
    inference(resolution,[status(thm)],[c_130,c_102])).

tff(c_297,plain,(
    ! [A_100,A_101] :
      ( ~ r2_hidden(A_100,A_101)
      | r2_hidden(A_100,k2_zfmisc_1(k1_relat_1(A_101),k2_relat_1(A_101)))
      | ~ r2_hidden(A_100,A_101)
      | ~ v1_relat_1(A_101) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_164])).

tff(c_48,plain,(
    ! [A_31,B_32,C_33] :
      ( r2_hidden(k1_mcart_1(A_31),B_32)
      | ~ r2_hidden(A_31,k2_zfmisc_1(B_32,C_33)) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_304,plain,(
    ! [A_102,A_103] :
      ( r2_hidden(k1_mcart_1(A_102),k1_relat_1(A_103))
      | ~ r2_hidden(A_102,A_103)
      | ~ v1_relat_1(A_103) ) ),
    inference(resolution,[status(thm)],[c_297,c_48])).

tff(c_50,plain,
    ( ~ r2_hidden(k2_mcart_1('#skF_4'),k2_relat_1('#skF_3'))
    | ~ r2_hidden(k1_mcart_1('#skF_4'),k1_relat_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_86,plain,(
    ~ r2_hidden(k1_mcart_1('#skF_4'),k1_relat_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_307,plain,
    ( ~ r2_hidden('#skF_4','#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_304,c_86])).

tff(c_311,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_307])).

tff(c_312,plain,(
    ~ r2_hidden(k2_mcart_1('#skF_4'),k2_relat_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_625,plain,
    ( ~ r2_hidden('#skF_4','#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_622,c_312])).

tff(c_629,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_625])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:40:23 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.92/1.48  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.92/1.49  
% 2.92/1.49  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.92/1.49  %$ r2_hidden > v1_relat_1 > k6_enumset1 > k5_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_relat_1 > k2_mcart_1 > k1_relat_1 > k1_mcart_1 > #skF_1 > #skF_3 > #skF_2 > #skF_4
% 2.92/1.49  
% 2.92/1.49  %Foreground sorts:
% 2.92/1.49  
% 2.92/1.49  
% 2.92/1.49  %Background operators:
% 2.92/1.49  
% 2.92/1.49  
% 2.92/1.49  %Foreground operators:
% 2.92/1.49  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.92/1.49  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.92/1.49  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.92/1.49  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.92/1.49  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.92/1.49  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.92/1.49  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.92/1.49  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.92/1.49  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.92/1.49  tff('#skF_3', type, '#skF_3': $i).
% 2.92/1.49  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.92/1.49  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.92/1.49  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.92/1.49  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 2.92/1.49  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.92/1.49  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.92/1.49  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.92/1.49  tff('#skF_4', type, '#skF_4': $i).
% 2.92/1.49  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.92/1.49  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 2.92/1.49  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.92/1.49  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.92/1.49  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.92/1.49  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.92/1.49  
% 3.04/1.50  tff(f_74, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (r2_hidden(B, A) => (r2_hidden(k1_mcart_1(B), k1_relat_1(A)) & r2_hidden(k2_mcart_1(B), k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_mcart_1)).
% 3.04/1.50  tff(f_58, axiom, (![A]: (v1_relat_1(A) => (k3_xboole_0(A, k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_relat_1)).
% 3.04/1.50  tff(f_42, axiom, (![A, B, C]: (r2_hidden(A, k5_xboole_0(B, C)) <=> ~(r2_hidden(A, B) <=> r2_hidden(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_0)).
% 3.04/1.50  tff(f_44, axiom, (![A, B]: (k5_xboole_0(A, B) = k4_xboole_0(k2_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t101_xboole_1)).
% 3.04/1.50  tff(f_35, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 3.04/1.50  tff(f_64, axiom, (![A, B, C]: (r2_hidden(A, k2_zfmisc_1(B, C)) => (r2_hidden(k1_mcart_1(A), B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_mcart_1)).
% 3.04/1.50  tff(c_54, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.04/1.50  tff(c_52, plain, (r2_hidden('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.04/1.50  tff(c_44, plain, (![A_30]: (k3_xboole_0(A_30, k2_zfmisc_1(k1_relat_1(A_30), k2_relat_1(A_30)))=A_30 | ~v1_relat_1(A_30))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.04/1.50  tff(c_352, plain, (![A_116, C_117, B_118]: (r2_hidden(A_116, C_117) | ~r2_hidden(A_116, B_118) | r2_hidden(A_116, k5_xboole_0(B_118, C_117)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.04/1.50  tff(c_314, plain, (![A_104, B_105]: (k4_xboole_0(k2_xboole_0(A_104, B_105), k3_xboole_0(A_104, B_105))=k5_xboole_0(A_104, B_105))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.04/1.50  tff(c_4, plain, (![D_6, B_2, A_1]: (~r2_hidden(D_6, B_2) | ~r2_hidden(D_6, k4_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.04/1.50  tff(c_320, plain, (![D_6, A_104, B_105]: (~r2_hidden(D_6, k3_xboole_0(A_104, B_105)) | ~r2_hidden(D_6, k5_xboole_0(A_104, B_105)))), inference(superposition, [status(thm), theory('equality')], [c_314, c_4])).
% 3.04/1.50  tff(c_395, plain, (![A_131, B_132, C_133]: (~r2_hidden(A_131, k3_xboole_0(B_132, C_133)) | r2_hidden(A_131, C_133) | ~r2_hidden(A_131, B_132))), inference(resolution, [status(thm)], [c_352, c_320])).
% 3.04/1.50  tff(c_458, plain, (![A_150, A_151]: (~r2_hidden(A_150, A_151) | r2_hidden(A_150, k2_zfmisc_1(k1_relat_1(A_151), k2_relat_1(A_151))) | ~r2_hidden(A_150, A_151) | ~v1_relat_1(A_151))), inference(superposition, [status(thm), theory('equality')], [c_44, c_395])).
% 3.04/1.50  tff(c_46, plain, (![A_31, C_33, B_32]: (r2_hidden(k2_mcart_1(A_31), C_33) | ~r2_hidden(A_31, k2_zfmisc_1(B_32, C_33)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.04/1.50  tff(c_622, plain, (![A_159, A_160]: (r2_hidden(k2_mcart_1(A_159), k2_relat_1(A_160)) | ~r2_hidden(A_159, A_160) | ~v1_relat_1(A_160))), inference(resolution, [status(thm)], [c_458, c_46])).
% 3.04/1.50  tff(c_130, plain, (![A_72, C_73, B_74]: (r2_hidden(A_72, C_73) | ~r2_hidden(A_72, B_74) | r2_hidden(A_72, k5_xboole_0(B_74, C_73)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.04/1.50  tff(c_96, plain, (![A_55, B_56]: (k4_xboole_0(k2_xboole_0(A_55, B_56), k3_xboole_0(A_55, B_56))=k5_xboole_0(A_55, B_56))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.04/1.50  tff(c_102, plain, (![D_6, A_55, B_56]: (~r2_hidden(D_6, k3_xboole_0(A_55, B_56)) | ~r2_hidden(D_6, k5_xboole_0(A_55, B_56)))), inference(superposition, [status(thm), theory('equality')], [c_96, c_4])).
% 3.04/1.50  tff(c_164, plain, (![A_78, B_79, C_80]: (~r2_hidden(A_78, k3_xboole_0(B_79, C_80)) | r2_hidden(A_78, C_80) | ~r2_hidden(A_78, B_79))), inference(resolution, [status(thm)], [c_130, c_102])).
% 3.04/1.50  tff(c_297, plain, (![A_100, A_101]: (~r2_hidden(A_100, A_101) | r2_hidden(A_100, k2_zfmisc_1(k1_relat_1(A_101), k2_relat_1(A_101))) | ~r2_hidden(A_100, A_101) | ~v1_relat_1(A_101))), inference(superposition, [status(thm), theory('equality')], [c_44, c_164])).
% 3.04/1.50  tff(c_48, plain, (![A_31, B_32, C_33]: (r2_hidden(k1_mcart_1(A_31), B_32) | ~r2_hidden(A_31, k2_zfmisc_1(B_32, C_33)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.04/1.50  tff(c_304, plain, (![A_102, A_103]: (r2_hidden(k1_mcart_1(A_102), k1_relat_1(A_103)) | ~r2_hidden(A_102, A_103) | ~v1_relat_1(A_103))), inference(resolution, [status(thm)], [c_297, c_48])).
% 3.04/1.50  tff(c_50, plain, (~r2_hidden(k2_mcart_1('#skF_4'), k2_relat_1('#skF_3')) | ~r2_hidden(k1_mcart_1('#skF_4'), k1_relat_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.04/1.50  tff(c_86, plain, (~r2_hidden(k1_mcart_1('#skF_4'), k1_relat_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_50])).
% 3.04/1.50  tff(c_307, plain, (~r2_hidden('#skF_4', '#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_304, c_86])).
% 3.04/1.50  tff(c_311, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_307])).
% 3.04/1.50  tff(c_312, plain, (~r2_hidden(k2_mcart_1('#skF_4'), k2_relat_1('#skF_3'))), inference(splitRight, [status(thm)], [c_50])).
% 3.04/1.50  tff(c_625, plain, (~r2_hidden('#skF_4', '#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_622, c_312])).
% 3.04/1.50  tff(c_629, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_625])).
% 3.04/1.50  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.04/1.50  
% 3.04/1.50  Inference rules
% 3.04/1.50  ----------------------
% 3.04/1.50  #Ref     : 0
% 3.04/1.50  #Sup     : 122
% 3.04/1.50  #Fact    : 0
% 3.04/1.50  #Define  : 0
% 3.04/1.50  #Split   : 1
% 3.04/1.50  #Chain   : 0
% 3.04/1.50  #Close   : 0
% 3.04/1.50  
% 3.04/1.50  Ordering : KBO
% 3.04/1.50  
% 3.04/1.50  Simplification rules
% 3.04/1.50  ----------------------
% 3.04/1.50  #Subsume      : 0
% 3.04/1.50  #Demod        : 4
% 3.04/1.50  #Tautology    : 38
% 3.04/1.50  #SimpNegUnit  : 0
% 3.04/1.50  #BackRed      : 0
% 3.04/1.50  
% 3.04/1.50  #Partial instantiations: 0
% 3.04/1.50  #Strategies tried      : 1
% 3.04/1.50  
% 3.04/1.50  Timing (in seconds)
% 3.04/1.50  ----------------------
% 3.04/1.50  Preprocessing        : 0.35
% 3.04/1.50  Parsing              : 0.19
% 3.04/1.50  CNF conversion       : 0.03
% 3.04/1.50  Main loop            : 0.35
% 3.04/1.50  Inferencing          : 0.14
% 3.04/1.50  Reduction            : 0.08
% 3.04/1.50  Demodulation         : 0.06
% 3.04/1.50  BG Simplification    : 0.02
% 3.04/1.50  Subsumption          : 0.07
% 3.04/1.50  Abstraction          : 0.02
% 3.04/1.51  MUC search           : 0.00
% 3.04/1.51  Cooper               : 0.00
% 3.04/1.51  Total                : 0.73
% 3.04/1.51  Index Insertion      : 0.00
% 3.04/1.51  Index Deletion       : 0.00
% 3.04/1.51  Index Matching       : 0.00
% 3.04/1.51  BG Taut test         : 0.00
%------------------------------------------------------------------------------
