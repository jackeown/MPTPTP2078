%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:40 EST 2020

% Result     : Theorem 20.35s
% Output     : CNFRefutation 20.35s
% Verified   : 
% Statistics : Number of formulae       :   56 (  73 expanded)
%              Number of leaves         :   27 (  36 expanded)
%              Depth                    :    8
%              Number of atoms          :   83 ( 117 expanded)
%              Number of equality atoms :    6 (  12 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > k4_tarski > k2_zfmisc_1 > k2_xboole_0 > #nlpp > k3_relat_1 > k2_relat_1 > k1_wellord2 > k1_relat_1 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k3_relat_1,type,(
    k3_relat_1: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k1_wellord2,type,(
    k1_wellord2: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_75,axiom,(
    ! [A] : v1_relat_1(k1_wellord2(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_wellord2)).

tff(f_73,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( B = k1_wellord2(A)
      <=> ( k3_relat_1(B) = A
          & ! [C,D] :
              ( ( r2_hidden(C,A)
                & r2_hidden(D,A) )
             => ( r2_hidden(k4_tarski(C,D),B)
              <=> r1_tarski(C,D) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_wellord2)).

tff(f_54,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k3_relat_1(A) = k2_xboole_0(k1_relat_1(A),k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_relat_1)).

tff(f_36,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(A,k2_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).

tff(f_44,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_58,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => r1_tarski(A,k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_relat_1)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => ( r1_tarski(k2_zfmisc_1(A,C),k2_zfmisc_1(B,C))
        & r1_tarski(k2_zfmisc_1(C,A),k2_zfmisc_1(C,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t118_zfmisc_1)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_78,negated_conjecture,(
    ~ ! [A] : r1_tarski(k1_wellord2(A),k2_zfmisc_1(A,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_wellord2)).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_62,plain,(
    ! [A_37,B_38] :
      ( ~ r2_hidden('#skF_1'(A_37,B_38),B_38)
      | r1_tarski(A_37,B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_67,plain,(
    ! [A_1] : r1_tarski(A_1,A_1) ),
    inference(resolution,[status(thm)],[c_6,c_62])).

tff(c_40,plain,(
    ! [A_27] : v1_relat_1(k1_wellord2(A_27)) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_34,plain,(
    ! [A_19] :
      ( k3_relat_1(k1_wellord2(A_19)) = A_19
      | ~ v1_relat_1(k1_wellord2(A_19)) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_48,plain,(
    ! [A_19] : k3_relat_1(k1_wellord2(A_19)) = A_19 ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_34])).

tff(c_91,plain,(
    ! [A_50] :
      ( k2_xboole_0(k1_relat_1(A_50),k2_relat_1(A_50)) = k3_relat_1(A_50)
      | ~ v1_relat_1(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_8,plain,(
    ! [A_6,C_8,B_7] :
      ( r1_tarski(A_6,k2_xboole_0(C_8,B_7))
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_160,plain,(
    ! [A_63,A_64] :
      ( r1_tarski(A_63,k3_relat_1(A_64))
      | ~ r1_tarski(A_63,k2_relat_1(A_64))
      | ~ v1_relat_1(A_64) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_91,c_8])).

tff(c_165,plain,(
    ! [A_63,A_19] :
      ( r1_tarski(A_63,A_19)
      | ~ r1_tarski(A_63,k2_relat_1(k1_wellord2(A_19)))
      | ~ v1_relat_1(k1_wellord2(A_19)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_160])).

tff(c_169,plain,(
    ! [A_65,A_66] :
      ( r1_tarski(A_65,A_66)
      | ~ r1_tarski(A_65,k2_relat_1(k1_wellord2(A_66))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_165])).

tff(c_189,plain,(
    ! [A_66] : r1_tarski(k2_relat_1(k1_wellord2(A_66)),A_66) ),
    inference(resolution,[status(thm)],[c_67,c_169])).

tff(c_12,plain,(
    ! [A_12,B_13] : r1_tarski(A_12,k2_xboole_0(A_12,B_13)) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_109,plain,(
    ! [A_51] :
      ( r1_tarski(k1_relat_1(A_51),k3_relat_1(A_51))
      | ~ v1_relat_1(A_51) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_91,c_12])).

tff(c_114,plain,(
    ! [A_19] :
      ( r1_tarski(k1_relat_1(k1_wellord2(A_19)),A_19)
      | ~ v1_relat_1(k1_wellord2(A_19)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_109])).

tff(c_117,plain,(
    ! [A_19] : r1_tarski(k1_relat_1(k1_wellord2(A_19)),A_19) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_114])).

tff(c_20,plain,(
    ! [A_18] :
      ( r1_tarski(A_18,k2_zfmisc_1(k1_relat_1(A_18),k2_relat_1(A_18)))
      | ~ v1_relat_1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_156,plain,(
    ! [C_60,A_61,B_62] :
      ( r1_tarski(k2_zfmisc_1(C_60,A_61),k2_zfmisc_1(C_60,B_62))
      | ~ r1_tarski(A_61,B_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_10,plain,(
    ! [A_9,C_11,B_10] :
      ( r1_tarski(A_9,C_11)
      | ~ r1_tarski(B_10,C_11)
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_1259,plain,(
    ! [A_158,C_159,B_160,A_161] :
      ( r1_tarski(A_158,k2_zfmisc_1(C_159,B_160))
      | ~ r1_tarski(A_158,k2_zfmisc_1(C_159,A_161))
      | ~ r1_tarski(A_161,B_160) ) ),
    inference(resolution,[status(thm)],[c_156,c_10])).

tff(c_2978,plain,(
    ! [A_272,B_273] :
      ( r1_tarski(A_272,k2_zfmisc_1(k1_relat_1(A_272),B_273))
      | ~ r1_tarski(k2_relat_1(A_272),B_273)
      | ~ v1_relat_1(A_272) ) ),
    inference(resolution,[status(thm)],[c_20,c_1259])).

tff(c_122,plain,(
    ! [A_53,C_54,B_55] :
      ( r1_tarski(k2_zfmisc_1(A_53,C_54),k2_zfmisc_1(B_55,C_54))
      | ~ r1_tarski(A_53,B_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_125,plain,(
    ! [A_9,B_55,C_54,A_53] :
      ( r1_tarski(A_9,k2_zfmisc_1(B_55,C_54))
      | ~ r1_tarski(A_9,k2_zfmisc_1(A_53,C_54))
      | ~ r1_tarski(A_53,B_55) ) ),
    inference(resolution,[status(thm)],[c_122,c_10])).

tff(c_43062,plain,(
    ! [A_1226,B_1227,B_1228] :
      ( r1_tarski(A_1226,k2_zfmisc_1(B_1227,B_1228))
      | ~ r1_tarski(k1_relat_1(A_1226),B_1227)
      | ~ r1_tarski(k2_relat_1(A_1226),B_1228)
      | ~ v1_relat_1(A_1226) ) ),
    inference(resolution,[status(thm)],[c_2978,c_125])).

tff(c_43507,plain,(
    ! [A_19,B_1228] :
      ( r1_tarski(k1_wellord2(A_19),k2_zfmisc_1(A_19,B_1228))
      | ~ r1_tarski(k2_relat_1(k1_wellord2(A_19)),B_1228)
      | ~ v1_relat_1(k1_wellord2(A_19)) ) ),
    inference(resolution,[status(thm)],[c_117,c_43062])).

tff(c_43957,plain,(
    ! [A_1229,B_1230] :
      ( r1_tarski(k1_wellord2(A_1229),k2_zfmisc_1(A_1229,B_1230))
      | ~ r1_tarski(k2_relat_1(k1_wellord2(A_1229)),B_1230) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_43507])).

tff(c_44512,plain,(
    ! [A_66] : r1_tarski(k1_wellord2(A_66),k2_zfmisc_1(A_66,A_66)) ),
    inference(resolution,[status(thm)],[c_189,c_43957])).

tff(c_42,plain,(
    ~ r1_tarski(k1_wellord2('#skF_4'),k2_zfmisc_1('#skF_4','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_44521,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44512,c_42])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:21:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 20.35/12.60  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 20.35/12.60  
% 20.35/12.60  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 20.35/12.60  %$ r2_hidden > r1_tarski > v1_relat_1 > k4_tarski > k2_zfmisc_1 > k2_xboole_0 > #nlpp > k3_relat_1 > k2_relat_1 > k1_wellord2 > k1_relat_1 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 20.35/12.60  
% 20.35/12.60  %Foreground sorts:
% 20.35/12.60  
% 20.35/12.60  
% 20.35/12.60  %Background operators:
% 20.35/12.60  
% 20.35/12.60  
% 20.35/12.60  %Foreground operators:
% 20.35/12.60  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 20.35/12.60  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 20.35/12.60  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 20.35/12.60  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 20.35/12.60  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 20.35/12.60  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 20.35/12.60  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 20.35/12.60  tff(k1_wellord2, type, k1_wellord2: $i > $i).
% 20.35/12.60  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 20.35/12.60  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 20.35/12.60  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 20.35/12.60  tff('#skF_4', type, '#skF_4': $i).
% 20.35/12.60  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 20.35/12.60  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 20.35/12.60  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 20.35/12.60  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 20.35/12.60  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 20.35/12.60  
% 20.35/12.62  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 20.35/12.62  tff(f_75, axiom, (![A]: v1_relat_1(k1_wellord2(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_wellord2)).
% 20.35/12.62  tff(f_73, axiom, (![A, B]: (v1_relat_1(B) => ((B = k1_wellord2(A)) <=> ((k3_relat_1(B) = A) & (![C, D]: ((r2_hidden(C, A) & r2_hidden(D, A)) => (r2_hidden(k4_tarski(C, D), B) <=> r1_tarski(C, D)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_wellord2)).
% 20.35/12.62  tff(f_54, axiom, (![A]: (v1_relat_1(A) => (k3_relat_1(A) = k2_xboole_0(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_relat_1)).
% 20.35/12.62  tff(f_36, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(A, k2_xboole_0(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_xboole_1)).
% 20.35/12.62  tff(f_44, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 20.35/12.62  tff(f_58, axiom, (![A]: (v1_relat_1(A) => r1_tarski(A, k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_relat_1)).
% 20.35/12.62  tff(f_50, axiom, (![A, B, C]: (r1_tarski(A, B) => (r1_tarski(k2_zfmisc_1(A, C), k2_zfmisc_1(B, C)) & r1_tarski(k2_zfmisc_1(C, A), k2_zfmisc_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t118_zfmisc_1)).
% 20.35/12.62  tff(f_42, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 20.35/12.62  tff(f_78, negated_conjecture, ~(![A]: r1_tarski(k1_wellord2(A), k2_zfmisc_1(A, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t33_wellord2)).
% 20.35/12.62  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 20.35/12.62  tff(c_62, plain, (![A_37, B_38]: (~r2_hidden('#skF_1'(A_37, B_38), B_38) | r1_tarski(A_37, B_38))), inference(cnfTransformation, [status(thm)], [f_32])).
% 20.35/12.62  tff(c_67, plain, (![A_1]: (r1_tarski(A_1, A_1))), inference(resolution, [status(thm)], [c_6, c_62])).
% 20.35/12.62  tff(c_40, plain, (![A_27]: (v1_relat_1(k1_wellord2(A_27)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 20.35/12.62  tff(c_34, plain, (![A_19]: (k3_relat_1(k1_wellord2(A_19))=A_19 | ~v1_relat_1(k1_wellord2(A_19)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 20.35/12.62  tff(c_48, plain, (![A_19]: (k3_relat_1(k1_wellord2(A_19))=A_19)), inference(demodulation, [status(thm), theory('equality')], [c_40, c_34])).
% 20.35/12.62  tff(c_91, plain, (![A_50]: (k2_xboole_0(k1_relat_1(A_50), k2_relat_1(A_50))=k3_relat_1(A_50) | ~v1_relat_1(A_50))), inference(cnfTransformation, [status(thm)], [f_54])).
% 20.35/12.62  tff(c_8, plain, (![A_6, C_8, B_7]: (r1_tarski(A_6, k2_xboole_0(C_8, B_7)) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_36])).
% 20.35/12.62  tff(c_160, plain, (![A_63, A_64]: (r1_tarski(A_63, k3_relat_1(A_64)) | ~r1_tarski(A_63, k2_relat_1(A_64)) | ~v1_relat_1(A_64))), inference(superposition, [status(thm), theory('equality')], [c_91, c_8])).
% 20.35/12.62  tff(c_165, plain, (![A_63, A_19]: (r1_tarski(A_63, A_19) | ~r1_tarski(A_63, k2_relat_1(k1_wellord2(A_19))) | ~v1_relat_1(k1_wellord2(A_19)))), inference(superposition, [status(thm), theory('equality')], [c_48, c_160])).
% 20.35/12.62  tff(c_169, plain, (![A_65, A_66]: (r1_tarski(A_65, A_66) | ~r1_tarski(A_65, k2_relat_1(k1_wellord2(A_66))))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_165])).
% 20.35/12.62  tff(c_189, plain, (![A_66]: (r1_tarski(k2_relat_1(k1_wellord2(A_66)), A_66))), inference(resolution, [status(thm)], [c_67, c_169])).
% 20.35/12.62  tff(c_12, plain, (![A_12, B_13]: (r1_tarski(A_12, k2_xboole_0(A_12, B_13)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 20.35/12.62  tff(c_109, plain, (![A_51]: (r1_tarski(k1_relat_1(A_51), k3_relat_1(A_51)) | ~v1_relat_1(A_51))), inference(superposition, [status(thm), theory('equality')], [c_91, c_12])).
% 20.35/12.62  tff(c_114, plain, (![A_19]: (r1_tarski(k1_relat_1(k1_wellord2(A_19)), A_19) | ~v1_relat_1(k1_wellord2(A_19)))), inference(superposition, [status(thm), theory('equality')], [c_48, c_109])).
% 20.35/12.62  tff(c_117, plain, (![A_19]: (r1_tarski(k1_relat_1(k1_wellord2(A_19)), A_19))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_114])).
% 20.35/12.62  tff(c_20, plain, (![A_18]: (r1_tarski(A_18, k2_zfmisc_1(k1_relat_1(A_18), k2_relat_1(A_18))) | ~v1_relat_1(A_18))), inference(cnfTransformation, [status(thm)], [f_58])).
% 20.35/12.62  tff(c_156, plain, (![C_60, A_61, B_62]: (r1_tarski(k2_zfmisc_1(C_60, A_61), k2_zfmisc_1(C_60, B_62)) | ~r1_tarski(A_61, B_62))), inference(cnfTransformation, [status(thm)], [f_50])).
% 20.35/12.62  tff(c_10, plain, (![A_9, C_11, B_10]: (r1_tarski(A_9, C_11) | ~r1_tarski(B_10, C_11) | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_42])).
% 20.35/12.62  tff(c_1259, plain, (![A_158, C_159, B_160, A_161]: (r1_tarski(A_158, k2_zfmisc_1(C_159, B_160)) | ~r1_tarski(A_158, k2_zfmisc_1(C_159, A_161)) | ~r1_tarski(A_161, B_160))), inference(resolution, [status(thm)], [c_156, c_10])).
% 20.35/12.62  tff(c_2978, plain, (![A_272, B_273]: (r1_tarski(A_272, k2_zfmisc_1(k1_relat_1(A_272), B_273)) | ~r1_tarski(k2_relat_1(A_272), B_273) | ~v1_relat_1(A_272))), inference(resolution, [status(thm)], [c_20, c_1259])).
% 20.35/12.62  tff(c_122, plain, (![A_53, C_54, B_55]: (r1_tarski(k2_zfmisc_1(A_53, C_54), k2_zfmisc_1(B_55, C_54)) | ~r1_tarski(A_53, B_55))), inference(cnfTransformation, [status(thm)], [f_50])).
% 20.35/12.62  tff(c_125, plain, (![A_9, B_55, C_54, A_53]: (r1_tarski(A_9, k2_zfmisc_1(B_55, C_54)) | ~r1_tarski(A_9, k2_zfmisc_1(A_53, C_54)) | ~r1_tarski(A_53, B_55))), inference(resolution, [status(thm)], [c_122, c_10])).
% 20.35/12.62  tff(c_43062, plain, (![A_1226, B_1227, B_1228]: (r1_tarski(A_1226, k2_zfmisc_1(B_1227, B_1228)) | ~r1_tarski(k1_relat_1(A_1226), B_1227) | ~r1_tarski(k2_relat_1(A_1226), B_1228) | ~v1_relat_1(A_1226))), inference(resolution, [status(thm)], [c_2978, c_125])).
% 20.35/12.62  tff(c_43507, plain, (![A_19, B_1228]: (r1_tarski(k1_wellord2(A_19), k2_zfmisc_1(A_19, B_1228)) | ~r1_tarski(k2_relat_1(k1_wellord2(A_19)), B_1228) | ~v1_relat_1(k1_wellord2(A_19)))), inference(resolution, [status(thm)], [c_117, c_43062])).
% 20.35/12.62  tff(c_43957, plain, (![A_1229, B_1230]: (r1_tarski(k1_wellord2(A_1229), k2_zfmisc_1(A_1229, B_1230)) | ~r1_tarski(k2_relat_1(k1_wellord2(A_1229)), B_1230))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_43507])).
% 20.35/12.62  tff(c_44512, plain, (![A_66]: (r1_tarski(k1_wellord2(A_66), k2_zfmisc_1(A_66, A_66)))), inference(resolution, [status(thm)], [c_189, c_43957])).
% 20.35/12.62  tff(c_42, plain, (~r1_tarski(k1_wellord2('#skF_4'), k2_zfmisc_1('#skF_4', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_78])).
% 20.35/12.62  tff(c_44521, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44512, c_42])).
% 20.35/12.62  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 20.35/12.62  
% 20.35/12.62  Inference rules
% 20.35/12.62  ----------------------
% 20.35/12.62  #Ref     : 0
% 20.35/12.62  #Sup     : 11848
% 20.35/12.62  #Fact    : 0
% 20.35/12.62  #Define  : 0
% 20.35/12.62  #Split   : 0
% 20.35/12.62  #Chain   : 0
% 20.35/12.62  #Close   : 0
% 20.35/12.62  
% 20.35/12.62  Ordering : KBO
% 20.35/12.62  
% 20.35/12.62  Simplification rules
% 20.35/12.62  ----------------------
% 20.35/12.62  #Subsume      : 82
% 20.35/12.62  #Demod        : 516
% 20.35/12.62  #Tautology    : 281
% 20.35/12.62  #SimpNegUnit  : 0
% 20.35/12.62  #BackRed      : 1
% 20.35/12.62  
% 20.35/12.62  #Partial instantiations: 0
% 20.35/12.62  #Strategies tried      : 1
% 20.35/12.62  
% 20.35/12.62  Timing (in seconds)
% 20.35/12.62  ----------------------
% 20.35/12.62  Preprocessing        : 0.31
% 20.35/12.62  Parsing              : 0.17
% 20.35/12.62  CNF conversion       : 0.02
% 20.35/12.62  Main loop            : 11.49
% 20.35/12.62  Inferencing          : 1.10
% 20.35/12.62  Reduction            : 3.94
% 20.35/12.62  Demodulation         : 3.47
% 20.35/12.62  BG Simplification    : 0.19
% 20.35/12.62  Subsumption          : 5.63
% 20.35/12.62  Abstraction          : 0.22
% 20.35/12.62  MUC search           : 0.00
% 20.35/12.62  Cooper               : 0.00
% 20.35/12.62  Total                : 11.83
% 20.35/12.62  Index Insertion      : 0.00
% 20.35/12.62  Index Deletion       : 0.00
% 20.35/12.62  Index Matching       : 0.00
% 20.35/12.62  BG Taut test         : 0.00
%------------------------------------------------------------------------------
