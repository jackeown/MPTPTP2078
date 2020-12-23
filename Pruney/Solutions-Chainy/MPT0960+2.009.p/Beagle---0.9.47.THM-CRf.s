%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:38 EST 2020

% Result     : Theorem 1.90s
% Output     : CNFRefutation 1.96s
% Verified   : 
% Statistics : Number of formulae       :   47 (  62 expanded)
%              Number of leaves         :   26 (  33 expanded)
%              Depth                    :    9
%              Number of atoms          :   56 (  80 expanded)
%              Number of equality atoms :    8 (  14 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > k4_tarski > k2_zfmisc_1 > k2_xboole_0 > #nlpp > k3_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_wellord2 > k1_relat_1 > #skF_3 > #skF_2 > #skF_1

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k1_wellord2,type,(
    k1_wellord2: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

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

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_62,axiom,(
    ! [A] : v1_relat_1(k1_wellord2(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_wellord2)).

tff(f_60,axiom,(
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

tff(f_37,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k3_relat_1(A) = k2_xboole_0(k1_relat_1(A),k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_relat_1)).

tff(f_29,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_65,negated_conjecture,(
    ~ ! [A] : r1_tarski(k1_wellord2(A),k2_zfmisc_1(A,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_wellord2)).

tff(c_32,plain,(
    ! [A_19] : v1_relat_1(k1_wellord2(A_19)) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_26,plain,(
    ! [A_11] :
      ( k3_relat_1(k1_wellord2(A_11)) = A_11
      | ~ v1_relat_1(k1_wellord2(A_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_40,plain,(
    ! [A_11] : k3_relat_1(k1_wellord2(A_11)) = A_11 ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_26])).

tff(c_107,plain,(
    ! [A_32] :
      ( k2_xboole_0(k1_relat_1(A_32),k2_relat_1(A_32)) = k3_relat_1(A_32)
      | ~ v1_relat_1(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_4,plain,(
    ! [A_3,B_4] : r1_tarski(A_3,k2_xboole_0(A_3,B_4)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_122,plain,(
    ! [A_33] :
      ( r1_tarski(k1_relat_1(A_33),k3_relat_1(A_33))
      | ~ v1_relat_1(A_33) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_107,c_4])).

tff(c_125,plain,(
    ! [A_11] :
      ( r1_tarski(k1_relat_1(k1_wellord2(A_11)),A_11)
      | ~ v1_relat_1(k1_wellord2(A_11)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_122])).

tff(c_127,plain,(
    ! [A_11] : r1_tarski(k1_relat_1(k1_wellord2(A_11)),A_11) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_125])).

tff(c_52,plain,(
    ! [B_24,A_25] : k2_xboole_0(B_24,A_25) = k2_xboole_0(A_25,B_24) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_67,plain,(
    ! [A_25,B_24] : r1_tarski(A_25,k2_xboole_0(B_24,A_25)) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_4])).

tff(c_129,plain,(
    ! [A_35] :
      ( r1_tarski(k2_relat_1(A_35),k3_relat_1(A_35))
      | ~ v1_relat_1(A_35) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_107,c_67])).

tff(c_132,plain,(
    ! [A_11] :
      ( r1_tarski(k2_relat_1(k1_wellord2(A_11)),A_11)
      | ~ v1_relat_1(k1_wellord2(A_11)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_129])).

tff(c_134,plain,(
    ! [A_11] : r1_tarski(k2_relat_1(k1_wellord2(A_11)),A_11) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_132])).

tff(c_164,plain,(
    ! [C_45,A_46,B_47] :
      ( m1_subset_1(C_45,k1_zfmisc_1(k2_zfmisc_1(A_46,B_47)))
      | ~ r1_tarski(k2_relat_1(C_45),B_47)
      | ~ r1_tarski(k1_relat_1(C_45),A_46)
      | ~ v1_relat_1(C_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_6,plain,(
    ! [A_5,B_6] :
      ( r1_tarski(A_5,B_6)
      | ~ m1_subset_1(A_5,k1_zfmisc_1(B_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_187,plain,(
    ! [C_49,A_50,B_51] :
      ( r1_tarski(C_49,k2_zfmisc_1(A_50,B_51))
      | ~ r1_tarski(k2_relat_1(C_49),B_51)
      | ~ r1_tarski(k1_relat_1(C_49),A_50)
      | ~ v1_relat_1(C_49) ) ),
    inference(resolution,[status(thm)],[c_164,c_6])).

tff(c_189,plain,(
    ! [A_11,A_50] :
      ( r1_tarski(k1_wellord2(A_11),k2_zfmisc_1(A_50,A_11))
      | ~ r1_tarski(k1_relat_1(k1_wellord2(A_11)),A_50)
      | ~ v1_relat_1(k1_wellord2(A_11)) ) ),
    inference(resolution,[status(thm)],[c_134,c_187])).

tff(c_204,plain,(
    ! [A_52,A_53] :
      ( r1_tarski(k1_wellord2(A_52),k2_zfmisc_1(A_53,A_52))
      | ~ r1_tarski(k1_relat_1(k1_wellord2(A_52)),A_53) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_189])).

tff(c_216,plain,(
    ! [A_11] : r1_tarski(k1_wellord2(A_11),k2_zfmisc_1(A_11,A_11)) ),
    inference(resolution,[status(thm)],[c_127,c_204])).

tff(c_34,plain,(
    ~ r1_tarski(k1_wellord2('#skF_3'),k2_zfmisc_1('#skF_3','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_224,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_216,c_34])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:56:42 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.90/1.19  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.90/1.19  
% 1.90/1.19  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.90/1.20  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > k4_tarski > k2_zfmisc_1 > k2_xboole_0 > #nlpp > k3_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_wellord2 > k1_relat_1 > #skF_3 > #skF_2 > #skF_1
% 1.90/1.20  
% 1.90/1.20  %Foreground sorts:
% 1.90/1.20  
% 1.90/1.20  
% 1.90/1.20  %Background operators:
% 1.90/1.20  
% 1.90/1.20  
% 1.90/1.20  %Foreground operators:
% 1.90/1.20  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.90/1.20  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.90/1.20  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.90/1.20  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 1.90/1.20  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.90/1.20  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.90/1.20  tff(k1_wellord2, type, k1_wellord2: $i > $i).
% 1.90/1.20  tff('#skF_3', type, '#skF_3': $i).
% 1.90/1.20  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.90/1.20  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.90/1.20  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.90/1.20  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.90/1.20  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.90/1.20  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.90/1.20  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.90/1.20  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.90/1.20  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.90/1.20  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.90/1.20  
% 1.96/1.21  tff(f_62, axiom, (![A]: v1_relat_1(k1_wellord2(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_wellord2)).
% 1.96/1.21  tff(f_60, axiom, (![A, B]: (v1_relat_1(B) => ((B = k1_wellord2(A)) <=> ((k3_relat_1(B) = A) & (![C, D]: ((r2_hidden(C, A) & r2_hidden(D, A)) => (r2_hidden(k4_tarski(C, D), B) <=> r1_tarski(C, D)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_wellord2)).
% 1.96/1.21  tff(f_37, axiom, (![A]: (v1_relat_1(A) => (k3_relat_1(A) = k2_xboole_0(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_relat_1)).
% 1.96/1.21  tff(f_29, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 1.96/1.21  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 1.96/1.21  tff(f_45, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_relset_1)).
% 1.96/1.21  tff(f_33, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 1.96/1.21  tff(f_65, negated_conjecture, ~(![A]: r1_tarski(k1_wellord2(A), k2_zfmisc_1(A, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t33_wellord2)).
% 1.96/1.21  tff(c_32, plain, (![A_19]: (v1_relat_1(k1_wellord2(A_19)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.96/1.21  tff(c_26, plain, (![A_11]: (k3_relat_1(k1_wellord2(A_11))=A_11 | ~v1_relat_1(k1_wellord2(A_11)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.96/1.21  tff(c_40, plain, (![A_11]: (k3_relat_1(k1_wellord2(A_11))=A_11)), inference(demodulation, [status(thm), theory('equality')], [c_32, c_26])).
% 1.96/1.21  tff(c_107, plain, (![A_32]: (k2_xboole_0(k1_relat_1(A_32), k2_relat_1(A_32))=k3_relat_1(A_32) | ~v1_relat_1(A_32))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.96/1.21  tff(c_4, plain, (![A_3, B_4]: (r1_tarski(A_3, k2_xboole_0(A_3, B_4)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.96/1.21  tff(c_122, plain, (![A_33]: (r1_tarski(k1_relat_1(A_33), k3_relat_1(A_33)) | ~v1_relat_1(A_33))), inference(superposition, [status(thm), theory('equality')], [c_107, c_4])).
% 1.96/1.21  tff(c_125, plain, (![A_11]: (r1_tarski(k1_relat_1(k1_wellord2(A_11)), A_11) | ~v1_relat_1(k1_wellord2(A_11)))), inference(superposition, [status(thm), theory('equality')], [c_40, c_122])).
% 1.96/1.21  tff(c_127, plain, (![A_11]: (r1_tarski(k1_relat_1(k1_wellord2(A_11)), A_11))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_125])).
% 1.96/1.21  tff(c_52, plain, (![B_24, A_25]: (k2_xboole_0(B_24, A_25)=k2_xboole_0(A_25, B_24))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.96/1.21  tff(c_67, plain, (![A_25, B_24]: (r1_tarski(A_25, k2_xboole_0(B_24, A_25)))), inference(superposition, [status(thm), theory('equality')], [c_52, c_4])).
% 1.96/1.21  tff(c_129, plain, (![A_35]: (r1_tarski(k2_relat_1(A_35), k3_relat_1(A_35)) | ~v1_relat_1(A_35))), inference(superposition, [status(thm), theory('equality')], [c_107, c_67])).
% 1.96/1.21  tff(c_132, plain, (![A_11]: (r1_tarski(k2_relat_1(k1_wellord2(A_11)), A_11) | ~v1_relat_1(k1_wellord2(A_11)))), inference(superposition, [status(thm), theory('equality')], [c_40, c_129])).
% 1.96/1.21  tff(c_134, plain, (![A_11]: (r1_tarski(k2_relat_1(k1_wellord2(A_11)), A_11))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_132])).
% 1.96/1.21  tff(c_164, plain, (![C_45, A_46, B_47]: (m1_subset_1(C_45, k1_zfmisc_1(k2_zfmisc_1(A_46, B_47))) | ~r1_tarski(k2_relat_1(C_45), B_47) | ~r1_tarski(k1_relat_1(C_45), A_46) | ~v1_relat_1(C_45))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.96/1.21  tff(c_6, plain, (![A_5, B_6]: (r1_tarski(A_5, B_6) | ~m1_subset_1(A_5, k1_zfmisc_1(B_6)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.96/1.21  tff(c_187, plain, (![C_49, A_50, B_51]: (r1_tarski(C_49, k2_zfmisc_1(A_50, B_51)) | ~r1_tarski(k2_relat_1(C_49), B_51) | ~r1_tarski(k1_relat_1(C_49), A_50) | ~v1_relat_1(C_49))), inference(resolution, [status(thm)], [c_164, c_6])).
% 1.96/1.21  tff(c_189, plain, (![A_11, A_50]: (r1_tarski(k1_wellord2(A_11), k2_zfmisc_1(A_50, A_11)) | ~r1_tarski(k1_relat_1(k1_wellord2(A_11)), A_50) | ~v1_relat_1(k1_wellord2(A_11)))), inference(resolution, [status(thm)], [c_134, c_187])).
% 1.96/1.21  tff(c_204, plain, (![A_52, A_53]: (r1_tarski(k1_wellord2(A_52), k2_zfmisc_1(A_53, A_52)) | ~r1_tarski(k1_relat_1(k1_wellord2(A_52)), A_53))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_189])).
% 1.96/1.21  tff(c_216, plain, (![A_11]: (r1_tarski(k1_wellord2(A_11), k2_zfmisc_1(A_11, A_11)))), inference(resolution, [status(thm)], [c_127, c_204])).
% 1.96/1.21  tff(c_34, plain, (~r1_tarski(k1_wellord2('#skF_3'), k2_zfmisc_1('#skF_3', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_65])).
% 1.96/1.21  tff(c_224, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_216, c_34])).
% 1.96/1.21  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.96/1.21  
% 1.96/1.21  Inference rules
% 1.96/1.21  ----------------------
% 1.96/1.21  #Ref     : 0
% 1.96/1.21  #Sup     : 38
% 1.96/1.21  #Fact    : 0
% 1.96/1.21  #Define  : 0
% 1.96/1.21  #Split   : 0
% 1.96/1.21  #Chain   : 0
% 1.96/1.21  #Close   : 0
% 1.96/1.21  
% 1.96/1.21  Ordering : KBO
% 1.96/1.21  
% 1.96/1.21  Simplification rules
% 1.96/1.21  ----------------------
% 1.96/1.21  #Subsume      : 0
% 1.96/1.21  #Demod        : 40
% 1.96/1.21  #Tautology    : 26
% 1.96/1.21  #SimpNegUnit  : 0
% 1.96/1.21  #BackRed      : 1
% 1.96/1.21  
% 1.96/1.21  #Partial instantiations: 0
% 1.96/1.21  #Strategies tried      : 1
% 1.96/1.21  
% 1.96/1.21  Timing (in seconds)
% 1.96/1.21  ----------------------
% 1.96/1.21  Preprocessing        : 0.28
% 1.96/1.21  Parsing              : 0.15
% 1.96/1.21  CNF conversion       : 0.02
% 1.96/1.21  Main loop            : 0.17
% 1.96/1.21  Inferencing          : 0.06
% 1.96/1.21  Reduction            : 0.07
% 1.96/1.21  Demodulation         : 0.05
% 1.96/1.21  BG Simplification    : 0.01
% 1.96/1.21  Subsumption          : 0.02
% 1.96/1.21  Abstraction          : 0.01
% 1.96/1.21  MUC search           : 0.00
% 1.96/1.21  Cooper               : 0.00
% 1.96/1.21  Total                : 0.48
% 1.96/1.21  Index Insertion      : 0.00
% 1.96/1.21  Index Deletion       : 0.00
% 1.96/1.21  Index Matching       : 0.00
% 1.96/1.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------
