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
% DateTime   : Thu Dec  3 10:10:39 EST 2020

% Result     : Theorem 2.23s
% Output     : CNFRefutation 2.23s
% Verified   : 
% Statistics : Number of formulae       :   49 (  62 expanded)
%              Number of leaves         :   27 (  33 expanded)
%              Depth                    :    9
%              Number of atoms          :   65 (  87 expanded)
%              Number of equality atoms :    7 (  13 expanded)
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

tff(f_70,axiom,(
    ! [A] : v1_relat_1(k1_wellord2(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_wellord2)).

tff(f_68,axiom,(
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

tff(f_45,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k3_relat_1(A) = k2_xboole_0(k1_relat_1(A),k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_relat_1)).

tff(f_37,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(A,k2_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_73,negated_conjecture,(
    ~ ! [A] : r1_tarski(k1_wellord2(A),k2_zfmisc_1(A,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_wellord2)).

tff(c_38,plain,(
    ! [A_22] : v1_relat_1(k1_wellord2(A_22)) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_32,plain,(
    ! [A_14] :
      ( k3_relat_1(k1_wellord2(A_14)) = A_14
      | ~ v1_relat_1(k1_wellord2(A_14)) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_46,plain,(
    ! [A_14] : k3_relat_1(k1_wellord2(A_14)) = A_14 ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_32])).

tff(c_80,plain,(
    ! [A_37] :
      ( k2_xboole_0(k1_relat_1(A_37),k2_relat_1(A_37)) = k3_relat_1(A_37)
      | ~ v1_relat_1(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_10,plain,(
    ! [A_6,B_7] : r1_tarski(A_6,k2_xboole_0(A_6,B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_95,plain,(
    ! [A_38] :
      ( r1_tarski(k1_relat_1(A_38),k3_relat_1(A_38))
      | ~ v1_relat_1(A_38) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_80,c_10])).

tff(c_100,plain,(
    ! [A_14] :
      ( r1_tarski(k1_relat_1(k1_wellord2(A_14)),A_14)
      | ~ v1_relat_1(k1_wellord2(A_14)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_95])).

tff(c_103,plain,(
    ! [A_14] : r1_tarski(k1_relat_1(k1_wellord2(A_14)),A_14) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_100])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_8,plain,(
    ! [A_3,C_5,B_4] :
      ( r1_tarski(A_3,k2_xboole_0(C_5,B_4))
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_118,plain,(
    ! [A_43,A_44] :
      ( r1_tarski(A_43,k3_relat_1(A_44))
      | ~ r1_tarski(A_43,k2_relat_1(A_44))
      | ~ v1_relat_1(A_44) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_80,c_8])).

tff(c_127,plain,(
    ! [A_43,A_14] :
      ( r1_tarski(A_43,A_14)
      | ~ r1_tarski(A_43,k2_relat_1(k1_wellord2(A_14)))
      | ~ v1_relat_1(k1_wellord2(A_14)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_118])).

tff(c_143,plain,(
    ! [A_46,A_47] :
      ( r1_tarski(A_46,A_47)
      | ~ r1_tarski(A_46,k2_relat_1(k1_wellord2(A_47))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_127])).

tff(c_153,plain,(
    ! [A_47] : r1_tarski(k2_relat_1(k1_wellord2(A_47)),A_47) ),
    inference(resolution,[status(thm)],[c_6,c_143])).

tff(c_261,plain,(
    ! [C_64,A_65,B_66] :
      ( m1_subset_1(C_64,k1_zfmisc_1(k2_zfmisc_1(A_65,B_66)))
      | ~ r1_tarski(k2_relat_1(C_64),B_66)
      | ~ r1_tarski(k1_relat_1(C_64),A_65)
      | ~ v1_relat_1(C_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_12,plain,(
    ! [A_8,B_9] :
      ( r1_tarski(A_8,B_9)
      | ~ m1_subset_1(A_8,k1_zfmisc_1(B_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_393,plain,(
    ! [C_80,A_81,B_82] :
      ( r1_tarski(C_80,k2_zfmisc_1(A_81,B_82))
      | ~ r1_tarski(k2_relat_1(C_80),B_82)
      | ~ r1_tarski(k1_relat_1(C_80),A_81)
      | ~ v1_relat_1(C_80) ) ),
    inference(resolution,[status(thm)],[c_261,c_12])).

tff(c_403,plain,(
    ! [A_47,A_81] :
      ( r1_tarski(k1_wellord2(A_47),k2_zfmisc_1(A_81,A_47))
      | ~ r1_tarski(k1_relat_1(k1_wellord2(A_47)),A_81)
      | ~ v1_relat_1(k1_wellord2(A_47)) ) ),
    inference(resolution,[status(thm)],[c_153,c_393])).

tff(c_435,plain,(
    ! [A_83,A_84] :
      ( r1_tarski(k1_wellord2(A_83),k2_zfmisc_1(A_84,A_83))
      | ~ r1_tarski(k1_relat_1(k1_wellord2(A_83)),A_84) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_403])).

tff(c_466,plain,(
    ! [A_14] : r1_tarski(k1_wellord2(A_14),k2_zfmisc_1(A_14,A_14)) ),
    inference(resolution,[status(thm)],[c_103,c_435])).

tff(c_40,plain,(
    ~ r1_tarski(k1_wellord2('#skF_3'),k2_zfmisc_1('#skF_3','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_475,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_466,c_40])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n001.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 21:15:30 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.23/1.28  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.23/1.29  
% 2.23/1.29  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.23/1.29  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > k4_tarski > k2_zfmisc_1 > k2_xboole_0 > #nlpp > k3_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_wellord2 > k1_relat_1 > #skF_3 > #skF_2 > #skF_1
% 2.23/1.29  
% 2.23/1.29  %Foreground sorts:
% 2.23/1.29  
% 2.23/1.29  
% 2.23/1.29  %Background operators:
% 2.23/1.29  
% 2.23/1.29  
% 2.23/1.29  %Foreground operators:
% 2.23/1.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.23/1.29  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.23/1.29  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.23/1.29  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 2.23/1.29  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.23/1.29  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.23/1.29  tff(k1_wellord2, type, k1_wellord2: $i > $i).
% 2.23/1.29  tff('#skF_3', type, '#skF_3': $i).
% 2.23/1.29  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.23/1.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.23/1.29  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.23/1.29  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.23/1.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.23/1.29  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.23/1.29  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.23/1.29  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.23/1.29  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.23/1.29  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.23/1.29  
% 2.23/1.30  tff(f_70, axiom, (![A]: v1_relat_1(k1_wellord2(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_wellord2)).
% 2.23/1.30  tff(f_68, axiom, (![A, B]: (v1_relat_1(B) => ((B = k1_wellord2(A)) <=> ((k3_relat_1(B) = A) & (![C, D]: ((r2_hidden(C, A) & r2_hidden(D, A)) => (r2_hidden(k4_tarski(C, D), B) <=> r1_tarski(C, D)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_wellord2)).
% 2.23/1.30  tff(f_45, axiom, (![A]: (v1_relat_1(A) => (k3_relat_1(A) = k2_xboole_0(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_relat_1)).
% 2.23/1.30  tff(f_37, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 2.23/1.30  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.23/1.30  tff(f_35, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(A, k2_xboole_0(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_xboole_1)).
% 2.23/1.30  tff(f_53, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_relset_1)).
% 2.23/1.30  tff(f_41, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 2.23/1.30  tff(f_73, negated_conjecture, ~(![A]: r1_tarski(k1_wellord2(A), k2_zfmisc_1(A, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t33_wellord2)).
% 2.23/1.30  tff(c_38, plain, (![A_22]: (v1_relat_1(k1_wellord2(A_22)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.23/1.30  tff(c_32, plain, (![A_14]: (k3_relat_1(k1_wellord2(A_14))=A_14 | ~v1_relat_1(k1_wellord2(A_14)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.23/1.30  tff(c_46, plain, (![A_14]: (k3_relat_1(k1_wellord2(A_14))=A_14)), inference(demodulation, [status(thm), theory('equality')], [c_38, c_32])).
% 2.23/1.30  tff(c_80, plain, (![A_37]: (k2_xboole_0(k1_relat_1(A_37), k2_relat_1(A_37))=k3_relat_1(A_37) | ~v1_relat_1(A_37))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.23/1.30  tff(c_10, plain, (![A_6, B_7]: (r1_tarski(A_6, k2_xboole_0(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.23/1.30  tff(c_95, plain, (![A_38]: (r1_tarski(k1_relat_1(A_38), k3_relat_1(A_38)) | ~v1_relat_1(A_38))), inference(superposition, [status(thm), theory('equality')], [c_80, c_10])).
% 2.23/1.30  tff(c_100, plain, (![A_14]: (r1_tarski(k1_relat_1(k1_wellord2(A_14)), A_14) | ~v1_relat_1(k1_wellord2(A_14)))), inference(superposition, [status(thm), theory('equality')], [c_46, c_95])).
% 2.23/1.30  tff(c_103, plain, (![A_14]: (r1_tarski(k1_relat_1(k1_wellord2(A_14)), A_14))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_100])).
% 2.23/1.30  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.23/1.30  tff(c_8, plain, (![A_3, C_5, B_4]: (r1_tarski(A_3, k2_xboole_0(C_5, B_4)) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.23/1.30  tff(c_118, plain, (![A_43, A_44]: (r1_tarski(A_43, k3_relat_1(A_44)) | ~r1_tarski(A_43, k2_relat_1(A_44)) | ~v1_relat_1(A_44))), inference(superposition, [status(thm), theory('equality')], [c_80, c_8])).
% 2.23/1.30  tff(c_127, plain, (![A_43, A_14]: (r1_tarski(A_43, A_14) | ~r1_tarski(A_43, k2_relat_1(k1_wellord2(A_14))) | ~v1_relat_1(k1_wellord2(A_14)))), inference(superposition, [status(thm), theory('equality')], [c_46, c_118])).
% 2.23/1.30  tff(c_143, plain, (![A_46, A_47]: (r1_tarski(A_46, A_47) | ~r1_tarski(A_46, k2_relat_1(k1_wellord2(A_47))))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_127])).
% 2.23/1.30  tff(c_153, plain, (![A_47]: (r1_tarski(k2_relat_1(k1_wellord2(A_47)), A_47))), inference(resolution, [status(thm)], [c_6, c_143])).
% 2.23/1.30  tff(c_261, plain, (![C_64, A_65, B_66]: (m1_subset_1(C_64, k1_zfmisc_1(k2_zfmisc_1(A_65, B_66))) | ~r1_tarski(k2_relat_1(C_64), B_66) | ~r1_tarski(k1_relat_1(C_64), A_65) | ~v1_relat_1(C_64))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.23/1.30  tff(c_12, plain, (![A_8, B_9]: (r1_tarski(A_8, B_9) | ~m1_subset_1(A_8, k1_zfmisc_1(B_9)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.23/1.30  tff(c_393, plain, (![C_80, A_81, B_82]: (r1_tarski(C_80, k2_zfmisc_1(A_81, B_82)) | ~r1_tarski(k2_relat_1(C_80), B_82) | ~r1_tarski(k1_relat_1(C_80), A_81) | ~v1_relat_1(C_80))), inference(resolution, [status(thm)], [c_261, c_12])).
% 2.23/1.30  tff(c_403, plain, (![A_47, A_81]: (r1_tarski(k1_wellord2(A_47), k2_zfmisc_1(A_81, A_47)) | ~r1_tarski(k1_relat_1(k1_wellord2(A_47)), A_81) | ~v1_relat_1(k1_wellord2(A_47)))), inference(resolution, [status(thm)], [c_153, c_393])).
% 2.23/1.30  tff(c_435, plain, (![A_83, A_84]: (r1_tarski(k1_wellord2(A_83), k2_zfmisc_1(A_84, A_83)) | ~r1_tarski(k1_relat_1(k1_wellord2(A_83)), A_84))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_403])).
% 2.23/1.30  tff(c_466, plain, (![A_14]: (r1_tarski(k1_wellord2(A_14), k2_zfmisc_1(A_14, A_14)))), inference(resolution, [status(thm)], [c_103, c_435])).
% 2.23/1.30  tff(c_40, plain, (~r1_tarski(k1_wellord2('#skF_3'), k2_zfmisc_1('#skF_3', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.23/1.30  tff(c_475, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_466, c_40])).
% 2.23/1.30  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.23/1.30  
% 2.23/1.30  Inference rules
% 2.23/1.30  ----------------------
% 2.23/1.30  #Ref     : 0
% 2.23/1.30  #Sup     : 89
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
% 2.23/1.30  #Subsume      : 4
% 2.23/1.30  #Demod        : 48
% 2.23/1.30  #Tautology    : 19
% 2.23/1.30  #SimpNegUnit  : 0
% 2.23/1.30  #BackRed      : 1
% 2.23/1.30  
% 2.23/1.30  #Partial instantiations: 0
% 2.23/1.30  #Strategies tried      : 1
% 2.23/1.30  
% 2.23/1.30  Timing (in seconds)
% 2.23/1.30  ----------------------
% 2.23/1.30  Preprocessing        : 0.28
% 2.23/1.30  Parsing              : 0.15
% 2.23/1.30  CNF conversion       : 0.02
% 2.23/1.30  Main loop            : 0.27
% 2.23/1.30  Inferencing          : 0.10
% 2.23/1.30  Reduction            : 0.08
% 2.23/1.30  Demodulation         : 0.06
% 2.23/1.30  BG Simplification    : 0.02
% 2.23/1.30  Subsumption          : 0.06
% 2.23/1.30  Abstraction          : 0.01
% 2.23/1.30  MUC search           : 0.00
% 2.23/1.30  Cooper               : 0.00
% 2.23/1.30  Total                : 0.58
% 2.23/1.30  Index Insertion      : 0.00
% 2.23/1.30  Index Deletion       : 0.00
% 2.23/1.30  Index Matching       : 0.00
% 2.23/1.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
