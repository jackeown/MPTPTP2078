%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:40 EST 2020

% Result     : Theorem 3.13s
% Output     : CNFRefutation 3.55s
% Verified   : 
% Statistics : Number of formulae       :   52 (  66 expanded)
%              Number of leaves         :   28 (  35 expanded)
%              Depth                    :    9
%              Number of atoms          :   69 (  94 expanded)
%              Number of equality atoms :    6 (  12 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > k4_tarski > k2_zfmisc_1 > k2_xboole_0 > #nlpp > k3_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_wellord2 > k1_relat_1 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

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

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_71,axiom,(
    ! [A] : v1_relat_1(k1_wellord2(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_wellord2)).

tff(f_69,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( B = k1_wellord2(A)
      <=> ( k3_relat_1(B) = A
          & ! [C,D] :
              ( ( r2_hidden(C,A)
                & r2_hidden(D,A) )
             => ( r2_hidden(k4_tarski(C,D),B)
              <=> r1_tarski(C,D) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_wellord2)).

tff(f_46,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k3_relat_1(A) = k2_xboole_0(k1_relat_1(A),k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_relat_1)).

tff(f_38,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_36,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(A,k2_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).

tff(f_54,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_74,negated_conjecture,(
    ~ ! [A] : r1_tarski(k1_wellord2(A),k2_zfmisc_1(A,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_wellord2)).

tff(c_38,plain,(
    ! [A_25] : v1_relat_1(k1_wellord2(A_25)) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_32,plain,(
    ! [A_17] :
      ( k3_relat_1(k1_wellord2(A_17)) = A_17
      | ~ v1_relat_1(k1_wellord2(A_17)) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_46,plain,(
    ! [A_17] : k3_relat_1(k1_wellord2(A_17)) = A_17 ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_32])).

tff(c_72,plain,(
    ! [A_41] :
      ( k2_xboole_0(k1_relat_1(A_41),k2_relat_1(A_41)) = k3_relat_1(A_41)
      | ~ v1_relat_1(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_10,plain,(
    ! [A_9,B_10] : r1_tarski(A_9,k2_xboole_0(A_9,B_10)) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_88,plain,(
    ! [A_43] :
      ( r1_tarski(k1_relat_1(A_43),k3_relat_1(A_43))
      | ~ v1_relat_1(A_43) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_10])).

tff(c_91,plain,(
    ! [A_17] :
      ( r1_tarski(k1_relat_1(k1_wellord2(A_17)),A_17)
      | ~ v1_relat_1(k1_wellord2(A_17)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_88])).

tff(c_93,plain,(
    ! [A_17] : r1_tarski(k1_relat_1(k1_wellord2(A_17)),A_17) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_91])).

tff(c_66,plain,(
    ! [A_39,B_40] :
      ( r2_hidden('#skF_1'(A_39,B_40),A_39)
      | r1_tarski(A_39,B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_71,plain,(
    ! [A_39] : r1_tarski(A_39,A_39) ),
    inference(resolution,[status(thm)],[c_66,c_4])).

tff(c_8,plain,(
    ! [A_6,C_8,B_7] :
      ( r1_tarski(A_6,k2_xboole_0(C_8,B_7))
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_99,plain,(
    ! [A_48,A_49] :
      ( r1_tarski(A_48,k3_relat_1(A_49))
      | ~ r1_tarski(A_48,k2_relat_1(A_49))
      | ~ v1_relat_1(A_49) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_8])).

tff(c_102,plain,(
    ! [A_48,A_17] :
      ( r1_tarski(A_48,A_17)
      | ~ r1_tarski(A_48,k2_relat_1(k1_wellord2(A_17)))
      | ~ v1_relat_1(k1_wellord2(A_17)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_99])).

tff(c_119,plain,(
    ! [A_51,A_52] :
      ( r1_tarski(A_51,A_52)
      | ~ r1_tarski(A_51,k2_relat_1(k1_wellord2(A_52))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_102])).

tff(c_129,plain,(
    ! [A_52] : r1_tarski(k2_relat_1(k1_wellord2(A_52)),A_52) ),
    inference(resolution,[status(thm)],[c_71,c_119])).

tff(c_211,plain,(
    ! [C_69,A_70,B_71] :
      ( m1_subset_1(C_69,k1_zfmisc_1(k2_zfmisc_1(A_70,B_71)))
      | ~ r1_tarski(k2_relat_1(C_69),B_71)
      | ~ r1_tarski(k1_relat_1(C_69),A_70)
      | ~ v1_relat_1(C_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_12,plain,(
    ! [A_11,B_12] :
      ( r1_tarski(A_11,B_12)
      | ~ m1_subset_1(A_11,k1_zfmisc_1(B_12)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_612,plain,(
    ! [C_106,A_107,B_108] :
      ( r1_tarski(C_106,k2_zfmisc_1(A_107,B_108))
      | ~ r1_tarski(k2_relat_1(C_106),B_108)
      | ~ r1_tarski(k1_relat_1(C_106),A_107)
      | ~ v1_relat_1(C_106) ) ),
    inference(resolution,[status(thm)],[c_211,c_12])).

tff(c_636,plain,(
    ! [A_52,A_107] :
      ( r1_tarski(k1_wellord2(A_52),k2_zfmisc_1(A_107,A_52))
      | ~ r1_tarski(k1_relat_1(k1_wellord2(A_52)),A_107)
      | ~ v1_relat_1(k1_wellord2(A_52)) ) ),
    inference(resolution,[status(thm)],[c_129,c_612])).

tff(c_682,plain,(
    ! [A_109,A_110] :
      ( r1_tarski(k1_wellord2(A_109),k2_zfmisc_1(A_110,A_109))
      | ~ r1_tarski(k1_relat_1(k1_wellord2(A_109)),A_110) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_636])).

tff(c_736,plain,(
    ! [A_17] : r1_tarski(k1_wellord2(A_17),k2_zfmisc_1(A_17,A_17)) ),
    inference(resolution,[status(thm)],[c_93,c_682])).

tff(c_40,plain,(
    ~ r1_tarski(k1_wellord2('#skF_4'),k2_zfmisc_1('#skF_4','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_745,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_736,c_40])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:47:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.13/1.76  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.13/1.76  
% 3.13/1.76  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.13/1.77  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > k4_tarski > k2_zfmisc_1 > k2_xboole_0 > #nlpp > k3_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_wellord2 > k1_relat_1 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 3.13/1.77  
% 3.13/1.77  %Foreground sorts:
% 3.13/1.77  
% 3.13/1.77  
% 3.13/1.77  %Background operators:
% 3.13/1.77  
% 3.13/1.77  
% 3.13/1.77  %Foreground operators:
% 3.13/1.77  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.13/1.77  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.13/1.77  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.13/1.77  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 3.13/1.77  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.13/1.77  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.13/1.77  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.13/1.77  tff(k1_wellord2, type, k1_wellord2: $i > $i).
% 3.13/1.77  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.13/1.77  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.13/1.77  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.13/1.77  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.13/1.77  tff('#skF_4', type, '#skF_4': $i).
% 3.13/1.77  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.13/1.77  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.13/1.77  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.13/1.77  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.13/1.77  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.13/1.77  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.13/1.77  
% 3.55/1.78  tff(f_71, axiom, (![A]: v1_relat_1(k1_wellord2(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_wellord2)).
% 3.55/1.78  tff(f_69, axiom, (![A, B]: (v1_relat_1(B) => ((B = k1_wellord2(A)) <=> ((k3_relat_1(B) = A) & (![C, D]: ((r2_hidden(C, A) & r2_hidden(D, A)) => (r2_hidden(k4_tarski(C, D), B) <=> r1_tarski(C, D)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_wellord2)).
% 3.55/1.78  tff(f_46, axiom, (![A]: (v1_relat_1(A) => (k3_relat_1(A) = k2_xboole_0(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_relat_1)).
% 3.55/1.78  tff(f_38, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 3.55/1.78  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 3.55/1.78  tff(f_36, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(A, k2_xboole_0(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_xboole_1)).
% 3.55/1.78  tff(f_54, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_relset_1)).
% 3.55/1.78  tff(f_42, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 3.55/1.78  tff(f_74, negated_conjecture, ~(![A]: r1_tarski(k1_wellord2(A), k2_zfmisc_1(A, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t33_wellord2)).
% 3.55/1.78  tff(c_38, plain, (![A_25]: (v1_relat_1(k1_wellord2(A_25)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.55/1.78  tff(c_32, plain, (![A_17]: (k3_relat_1(k1_wellord2(A_17))=A_17 | ~v1_relat_1(k1_wellord2(A_17)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.55/1.78  tff(c_46, plain, (![A_17]: (k3_relat_1(k1_wellord2(A_17))=A_17)), inference(demodulation, [status(thm), theory('equality')], [c_38, c_32])).
% 3.55/1.78  tff(c_72, plain, (![A_41]: (k2_xboole_0(k1_relat_1(A_41), k2_relat_1(A_41))=k3_relat_1(A_41) | ~v1_relat_1(A_41))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.55/1.78  tff(c_10, plain, (![A_9, B_10]: (r1_tarski(A_9, k2_xboole_0(A_9, B_10)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.55/1.78  tff(c_88, plain, (![A_43]: (r1_tarski(k1_relat_1(A_43), k3_relat_1(A_43)) | ~v1_relat_1(A_43))), inference(superposition, [status(thm), theory('equality')], [c_72, c_10])).
% 3.55/1.78  tff(c_91, plain, (![A_17]: (r1_tarski(k1_relat_1(k1_wellord2(A_17)), A_17) | ~v1_relat_1(k1_wellord2(A_17)))), inference(superposition, [status(thm), theory('equality')], [c_46, c_88])).
% 3.55/1.78  tff(c_93, plain, (![A_17]: (r1_tarski(k1_relat_1(k1_wellord2(A_17)), A_17))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_91])).
% 3.55/1.78  tff(c_66, plain, (![A_39, B_40]: (r2_hidden('#skF_1'(A_39, B_40), A_39) | r1_tarski(A_39, B_40))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.55/1.78  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.55/1.78  tff(c_71, plain, (![A_39]: (r1_tarski(A_39, A_39))), inference(resolution, [status(thm)], [c_66, c_4])).
% 3.55/1.78  tff(c_8, plain, (![A_6, C_8, B_7]: (r1_tarski(A_6, k2_xboole_0(C_8, B_7)) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.55/1.78  tff(c_99, plain, (![A_48, A_49]: (r1_tarski(A_48, k3_relat_1(A_49)) | ~r1_tarski(A_48, k2_relat_1(A_49)) | ~v1_relat_1(A_49))), inference(superposition, [status(thm), theory('equality')], [c_72, c_8])).
% 3.55/1.78  tff(c_102, plain, (![A_48, A_17]: (r1_tarski(A_48, A_17) | ~r1_tarski(A_48, k2_relat_1(k1_wellord2(A_17))) | ~v1_relat_1(k1_wellord2(A_17)))), inference(superposition, [status(thm), theory('equality')], [c_46, c_99])).
% 3.55/1.78  tff(c_119, plain, (![A_51, A_52]: (r1_tarski(A_51, A_52) | ~r1_tarski(A_51, k2_relat_1(k1_wellord2(A_52))))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_102])).
% 3.55/1.78  tff(c_129, plain, (![A_52]: (r1_tarski(k2_relat_1(k1_wellord2(A_52)), A_52))), inference(resolution, [status(thm)], [c_71, c_119])).
% 3.55/1.78  tff(c_211, plain, (![C_69, A_70, B_71]: (m1_subset_1(C_69, k1_zfmisc_1(k2_zfmisc_1(A_70, B_71))) | ~r1_tarski(k2_relat_1(C_69), B_71) | ~r1_tarski(k1_relat_1(C_69), A_70) | ~v1_relat_1(C_69))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.55/1.78  tff(c_12, plain, (![A_11, B_12]: (r1_tarski(A_11, B_12) | ~m1_subset_1(A_11, k1_zfmisc_1(B_12)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.55/1.78  tff(c_612, plain, (![C_106, A_107, B_108]: (r1_tarski(C_106, k2_zfmisc_1(A_107, B_108)) | ~r1_tarski(k2_relat_1(C_106), B_108) | ~r1_tarski(k1_relat_1(C_106), A_107) | ~v1_relat_1(C_106))), inference(resolution, [status(thm)], [c_211, c_12])).
% 3.55/1.78  tff(c_636, plain, (![A_52, A_107]: (r1_tarski(k1_wellord2(A_52), k2_zfmisc_1(A_107, A_52)) | ~r1_tarski(k1_relat_1(k1_wellord2(A_52)), A_107) | ~v1_relat_1(k1_wellord2(A_52)))), inference(resolution, [status(thm)], [c_129, c_612])).
% 3.55/1.78  tff(c_682, plain, (![A_109, A_110]: (r1_tarski(k1_wellord2(A_109), k2_zfmisc_1(A_110, A_109)) | ~r1_tarski(k1_relat_1(k1_wellord2(A_109)), A_110))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_636])).
% 3.55/1.78  tff(c_736, plain, (![A_17]: (r1_tarski(k1_wellord2(A_17), k2_zfmisc_1(A_17, A_17)))), inference(resolution, [status(thm)], [c_93, c_682])).
% 3.55/1.78  tff(c_40, plain, (~r1_tarski(k1_wellord2('#skF_4'), k2_zfmisc_1('#skF_4', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.55/1.78  tff(c_745, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_736, c_40])).
% 3.55/1.78  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.55/1.78  
% 3.55/1.78  Inference rules
% 3.55/1.78  ----------------------
% 3.55/1.78  #Ref     : 0
% 3.55/1.78  #Sup     : 155
% 3.55/1.78  #Fact    : 0
% 3.55/1.78  #Define  : 0
% 3.55/1.78  #Split   : 0
% 3.55/1.78  #Chain   : 0
% 3.55/1.78  #Close   : 0
% 3.55/1.78  
% 3.55/1.78  Ordering : KBO
% 3.55/1.78  
% 3.55/1.78  Simplification rules
% 3.55/1.78  ----------------------
% 3.55/1.78  #Subsume      : 1
% 3.55/1.78  #Demod        : 64
% 3.55/1.78  #Tautology    : 22
% 3.55/1.78  #SimpNegUnit  : 0
% 3.55/1.78  #BackRed      : 1
% 3.55/1.78  
% 3.55/1.78  #Partial instantiations: 0
% 3.55/1.78  #Strategies tried      : 1
% 3.55/1.78  
% 3.55/1.78  Timing (in seconds)
% 3.55/1.78  ----------------------
% 3.55/1.78  Preprocessing        : 0.38
% 3.55/1.78  Parsing              : 0.21
% 3.55/1.79  CNF conversion       : 0.03
% 3.55/1.79  Main loop            : 0.50
% 3.55/1.79  Inferencing          : 0.19
% 3.55/1.79  Reduction            : 0.16
% 3.55/1.79  Demodulation         : 0.12
% 3.55/1.79  BG Simplification    : 0.03
% 3.55/1.79  Subsumption          : 0.11
% 3.55/1.79  Abstraction          : 0.02
% 3.55/1.79  MUC search           : 0.00
% 3.55/1.79  Cooper               : 0.00
% 3.55/1.79  Total                : 0.92
% 3.55/1.79  Index Insertion      : 0.00
% 3.55/1.79  Index Deletion       : 0.00
% 3.55/1.79  Index Matching       : 0.00
% 3.55/1.79  BG Taut test         : 0.00
%------------------------------------------------------------------------------
