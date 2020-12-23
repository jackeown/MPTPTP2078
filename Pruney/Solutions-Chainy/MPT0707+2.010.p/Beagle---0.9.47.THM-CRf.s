%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:17 EST 2020

% Result     : Theorem 2.00s
% Output     : CNFRefutation 2.00s
% Verified   : 
% Statistics : Number of formulae       :   56 (  72 expanded)
%              Number of leaves         :   29 (  38 expanded)
%              Depth                    :    8
%              Number of atoms          :   66 (  87 expanded)
%              Number of equality atoms :   26 (  42 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k9_relat_1 > k5_relat_1 > k3_xboole_0 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_69,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => k9_relat_1(k6_relat_1(A),B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t162_funct_1)).

tff(f_37,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_34,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_56,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_45,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_64,axiom,(
    ! [A,B] : k5_relat_1(k6_relat_1(B),k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k5_relat_1(B,k6_relat_1(A)) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_52,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k2_relat_1(k5_relat_1(A,B)) = k9_relat_1(B,k2_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t160_relat_1)).

tff(c_34,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_16,plain,(
    ! [A_8] : ~ v1_xboole_0(k1_zfmisc_1(A_8)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_94,plain,(
    ! [A_30,B_31] :
      ( r2_hidden(A_30,B_31)
      | v1_xboole_0(B_31)
      | ~ m1_subset_1(A_30,B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_4,plain,(
    ! [C_7,A_3] :
      ( r1_tarski(C_7,A_3)
      | ~ r2_hidden(C_7,k1_zfmisc_1(A_3)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_98,plain,(
    ! [A_30,A_3] :
      ( r1_tarski(A_30,A_3)
      | v1_xboole_0(k1_zfmisc_1(A_3))
      | ~ m1_subset_1(A_30,k1_zfmisc_1(A_3)) ) ),
    inference(resolution,[status(thm)],[c_94,c_4])).

tff(c_102,plain,(
    ! [A_32,A_33] :
      ( r1_tarski(A_32,A_33)
      | ~ m1_subset_1(A_32,k1_zfmisc_1(A_33)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_16,c_98])).

tff(c_106,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_102])).

tff(c_24,plain,(
    ! [A_15] : k1_relat_1(k6_relat_1(A_15)) = A_15 ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_20,plain,(
    ! [A_11] : v1_relat_1(k6_relat_1(A_11)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_30,plain,(
    ! [B_19,A_18] : k5_relat_1(k6_relat_1(B_19),k6_relat_1(A_18)) = k6_relat_1(k3_xboole_0(A_18,B_19)) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_26,plain,(
    ! [A_15] : k2_relat_1(k6_relat_1(A_15)) = A_15 ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_116,plain,(
    ! [B_36,A_37] :
      ( k5_relat_1(B_36,k6_relat_1(A_37)) = B_36
      | ~ r1_tarski(k2_relat_1(B_36),A_37)
      | ~ v1_relat_1(B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_119,plain,(
    ! [A_15,A_37] :
      ( k5_relat_1(k6_relat_1(A_15),k6_relat_1(A_37)) = k6_relat_1(A_15)
      | ~ r1_tarski(A_15,A_37)
      | ~ v1_relat_1(k6_relat_1(A_15)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_116])).

tff(c_122,plain,(
    ! [A_38,A_39] :
      ( k6_relat_1(k3_xboole_0(A_38,A_39)) = k6_relat_1(A_39)
      | ~ r1_tarski(A_39,A_38) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_30,c_119])).

tff(c_134,plain,(
    ! [A_38,A_39] :
      ( k3_xboole_0(A_38,A_39) = k1_relat_1(k6_relat_1(A_39))
      | ~ r1_tarski(A_39,A_38) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_122,c_24])).

tff(c_170,plain,(
    ! [A_42,A_43] :
      ( k3_xboole_0(A_42,A_43) = A_43
      | ~ r1_tarski(A_43,A_42) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_134])).

tff(c_174,plain,(
    k3_xboole_0('#skF_3','#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_106,c_170])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_181,plain,(
    k3_xboole_0('#skF_4','#skF_3') = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_174,c_2])).

tff(c_156,plain,(
    ! [B_40,A_41] :
      ( k9_relat_1(B_40,k2_relat_1(A_41)) = k2_relat_1(k5_relat_1(A_41,B_40))
      | ~ v1_relat_1(B_40)
      | ~ v1_relat_1(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_165,plain,(
    ! [A_15,B_40] :
      ( k2_relat_1(k5_relat_1(k6_relat_1(A_15),B_40)) = k9_relat_1(B_40,A_15)
      | ~ v1_relat_1(B_40)
      | ~ v1_relat_1(k6_relat_1(A_15)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_156])).

tff(c_287,plain,(
    ! [A_52,B_53] :
      ( k2_relat_1(k5_relat_1(k6_relat_1(A_52),B_53)) = k9_relat_1(B_53,A_52)
      | ~ v1_relat_1(B_53) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_165])).

tff(c_308,plain,(
    ! [A_18,B_19] :
      ( k2_relat_1(k6_relat_1(k3_xboole_0(A_18,B_19))) = k9_relat_1(k6_relat_1(A_18),B_19)
      | ~ v1_relat_1(k6_relat_1(A_18)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_287])).

tff(c_312,plain,(
    ! [A_18,B_19] : k9_relat_1(k6_relat_1(A_18),B_19) = k3_xboole_0(A_18,B_19) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_26,c_308])).

tff(c_32,plain,(
    k9_relat_1(k6_relat_1('#skF_3'),'#skF_4') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_313,plain,(
    k3_xboole_0('#skF_3','#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_312,c_32])).

tff(c_316,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_181,c_2,c_313])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.11  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.32  % Computer   : n021.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % DateTime   : Tue Dec  1 21:06:19 EST 2020
% 0.11/0.32  % CPUTime    : 
% 0.11/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.00/1.28  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.00/1.28  
% 2.00/1.28  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.00/1.29  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k9_relat_1 > k5_relat_1 > k3_xboole_0 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.00/1.29  
% 2.00/1.29  %Foreground sorts:
% 2.00/1.29  
% 2.00/1.29  
% 2.00/1.29  %Background operators:
% 2.00/1.29  
% 2.00/1.29  
% 2.00/1.29  %Foreground operators:
% 2.00/1.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.00/1.29  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.00/1.29  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.00/1.29  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.00/1.29  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.00/1.29  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.00/1.29  tff('#skF_3', type, '#skF_3': $i).
% 2.00/1.29  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.00/1.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.00/1.29  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.00/1.29  tff('#skF_4', type, '#skF_4': $i).
% 2.00/1.29  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.00/1.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.00/1.29  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.00/1.29  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.00/1.29  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.00/1.29  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.00/1.29  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.00/1.29  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.00/1.29  
% 2.00/1.30  tff(f_69, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k9_relat_1(k6_relat_1(A), B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t162_funct_1)).
% 2.00/1.30  tff(f_37, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 2.00/1.30  tff(f_43, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 2.00/1.30  tff(f_34, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 2.00/1.30  tff(f_56, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 2.00/1.30  tff(f_45, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 2.00/1.30  tff(f_64, axiom, (![A, B]: (k5_relat_1(k6_relat_1(B), k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_funct_1)).
% 2.00/1.30  tff(f_62, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k5_relat_1(B, k6_relat_1(A)) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_relat_1)).
% 2.00/1.30  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.00/1.30  tff(f_52, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k2_relat_1(k5_relat_1(A, B)) = k9_relat_1(B, k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t160_relat_1)).
% 2.00/1.30  tff(c_34, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.00/1.30  tff(c_16, plain, (![A_8]: (~v1_xboole_0(k1_zfmisc_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.00/1.30  tff(c_94, plain, (![A_30, B_31]: (r2_hidden(A_30, B_31) | v1_xboole_0(B_31) | ~m1_subset_1(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.00/1.30  tff(c_4, plain, (![C_7, A_3]: (r1_tarski(C_7, A_3) | ~r2_hidden(C_7, k1_zfmisc_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.00/1.30  tff(c_98, plain, (![A_30, A_3]: (r1_tarski(A_30, A_3) | v1_xboole_0(k1_zfmisc_1(A_3)) | ~m1_subset_1(A_30, k1_zfmisc_1(A_3)))), inference(resolution, [status(thm)], [c_94, c_4])).
% 2.00/1.30  tff(c_102, plain, (![A_32, A_33]: (r1_tarski(A_32, A_33) | ~m1_subset_1(A_32, k1_zfmisc_1(A_33)))), inference(negUnitSimplification, [status(thm)], [c_16, c_98])).
% 2.00/1.30  tff(c_106, plain, (r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_34, c_102])).
% 2.00/1.30  tff(c_24, plain, (![A_15]: (k1_relat_1(k6_relat_1(A_15))=A_15)), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.00/1.30  tff(c_20, plain, (![A_11]: (v1_relat_1(k6_relat_1(A_11)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.00/1.30  tff(c_30, plain, (![B_19, A_18]: (k5_relat_1(k6_relat_1(B_19), k6_relat_1(A_18))=k6_relat_1(k3_xboole_0(A_18, B_19)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.00/1.30  tff(c_26, plain, (![A_15]: (k2_relat_1(k6_relat_1(A_15))=A_15)), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.00/1.30  tff(c_116, plain, (![B_36, A_37]: (k5_relat_1(B_36, k6_relat_1(A_37))=B_36 | ~r1_tarski(k2_relat_1(B_36), A_37) | ~v1_relat_1(B_36))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.00/1.30  tff(c_119, plain, (![A_15, A_37]: (k5_relat_1(k6_relat_1(A_15), k6_relat_1(A_37))=k6_relat_1(A_15) | ~r1_tarski(A_15, A_37) | ~v1_relat_1(k6_relat_1(A_15)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_116])).
% 2.00/1.30  tff(c_122, plain, (![A_38, A_39]: (k6_relat_1(k3_xboole_0(A_38, A_39))=k6_relat_1(A_39) | ~r1_tarski(A_39, A_38))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_30, c_119])).
% 2.00/1.30  tff(c_134, plain, (![A_38, A_39]: (k3_xboole_0(A_38, A_39)=k1_relat_1(k6_relat_1(A_39)) | ~r1_tarski(A_39, A_38))), inference(superposition, [status(thm), theory('equality')], [c_122, c_24])).
% 2.00/1.30  tff(c_170, plain, (![A_42, A_43]: (k3_xboole_0(A_42, A_43)=A_43 | ~r1_tarski(A_43, A_42))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_134])).
% 2.00/1.30  tff(c_174, plain, (k3_xboole_0('#skF_3', '#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_106, c_170])).
% 2.00/1.30  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.00/1.30  tff(c_181, plain, (k3_xboole_0('#skF_4', '#skF_3')='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_174, c_2])).
% 2.00/1.30  tff(c_156, plain, (![B_40, A_41]: (k9_relat_1(B_40, k2_relat_1(A_41))=k2_relat_1(k5_relat_1(A_41, B_40)) | ~v1_relat_1(B_40) | ~v1_relat_1(A_41))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.00/1.30  tff(c_165, plain, (![A_15, B_40]: (k2_relat_1(k5_relat_1(k6_relat_1(A_15), B_40))=k9_relat_1(B_40, A_15) | ~v1_relat_1(B_40) | ~v1_relat_1(k6_relat_1(A_15)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_156])).
% 2.00/1.30  tff(c_287, plain, (![A_52, B_53]: (k2_relat_1(k5_relat_1(k6_relat_1(A_52), B_53))=k9_relat_1(B_53, A_52) | ~v1_relat_1(B_53))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_165])).
% 2.00/1.30  tff(c_308, plain, (![A_18, B_19]: (k2_relat_1(k6_relat_1(k3_xboole_0(A_18, B_19)))=k9_relat_1(k6_relat_1(A_18), B_19) | ~v1_relat_1(k6_relat_1(A_18)))), inference(superposition, [status(thm), theory('equality')], [c_30, c_287])).
% 2.00/1.30  tff(c_312, plain, (![A_18, B_19]: (k9_relat_1(k6_relat_1(A_18), B_19)=k3_xboole_0(A_18, B_19))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_26, c_308])).
% 2.00/1.30  tff(c_32, plain, (k9_relat_1(k6_relat_1('#skF_3'), '#skF_4')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.00/1.30  tff(c_313, plain, (k3_xboole_0('#skF_3', '#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_312, c_32])).
% 2.00/1.30  tff(c_316, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_181, c_2, c_313])).
% 2.00/1.30  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.00/1.30  
% 2.00/1.30  Inference rules
% 2.00/1.30  ----------------------
% 2.00/1.30  #Ref     : 0
% 2.00/1.30  #Sup     : 67
% 2.00/1.30  #Fact    : 0
% 2.00/1.30  #Define  : 0
% 2.00/1.30  #Split   : 1
% 2.00/1.30  #Chain   : 0
% 2.00/1.30  #Close   : 0
% 2.00/1.30  
% 2.00/1.30  Ordering : KBO
% 2.00/1.30  
% 2.00/1.30  Simplification rules
% 2.00/1.30  ----------------------
% 2.00/1.30  #Subsume      : 6
% 2.00/1.30  #Demod        : 25
% 2.00/1.30  #Tautology    : 35
% 2.00/1.30  #SimpNegUnit  : 1
% 2.00/1.30  #BackRed      : 1
% 2.00/1.30  
% 2.00/1.30  #Partial instantiations: 0
% 2.00/1.30  #Strategies tried      : 1
% 2.00/1.30  
% 2.00/1.30  Timing (in seconds)
% 2.00/1.30  ----------------------
% 2.00/1.30  Preprocessing        : 0.33
% 2.00/1.30  Parsing              : 0.17
% 2.00/1.30  CNF conversion       : 0.02
% 2.00/1.30  Main loop            : 0.19
% 2.00/1.30  Inferencing          : 0.07
% 2.00/1.30  Reduction            : 0.07
% 2.00/1.30  Demodulation         : 0.05
% 2.00/1.30  BG Simplification    : 0.01
% 2.00/1.30  Subsumption          : 0.03
% 2.00/1.30  Abstraction          : 0.01
% 2.00/1.30  MUC search           : 0.00
% 2.00/1.30  Cooper               : 0.00
% 2.00/1.30  Total                : 0.54
% 2.00/1.30  Index Insertion      : 0.00
% 2.00/1.30  Index Deletion       : 0.00
% 2.00/1.30  Index Matching       : 0.00
% 2.00/1.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
