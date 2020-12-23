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
% DateTime   : Thu Dec  3 09:58:45 EST 2020

% Result     : Theorem 2.06s
% Output     : CNFRefutation 2.06s
% Verified   : 
% Statistics : Number of formulae       :   58 (  93 expanded)
%              Number of leaves         :   28 (  45 expanded)
%              Depth                    :    7
%              Number of atoms          :   79 ( 170 expanded)
%              Number of equality atoms :    6 (  15 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > k2_enumset1 > k1_enumset1 > k5_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_setfam_1 > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_86,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => ! [C] :
                ( v1_relat_1(C)
               => r1_tarski(k5_relat_1(A,k3_xboole_0(B,C)),k3_xboole_0(k5_relat_1(A,B),k5_relat_1(A,C))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_relat_1)).

tff(f_48,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

tff(f_56,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(k1_setfam_1(B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_setfam_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_63,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_75,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => ( r1_tarski(A,B)
               => r1_tarski(k5_relat_1(C,A),k5_relat_1(C,B)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C) )
     => r1_tarski(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).

tff(c_42,plain,(
    v1_relat_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_28,plain,(
    ! [A_17,B_18] : k1_setfam_1(k2_tarski(A_17,B_18)) = k3_xboole_0(A_17,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_8,plain,(
    ! [D_11,A_6] : r2_hidden(D_11,k2_tarski(A_6,D_11)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_34,plain,(
    ! [B_22,A_21] :
      ( r1_tarski(k1_setfam_1(B_22),A_21)
      | ~ r2_hidden(A_21,B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_32,plain,(
    ! [A_19,B_20] :
      ( m1_subset_1(A_19,k1_zfmisc_1(B_20))
      | ~ r1_tarski(A_19,B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_78,plain,(
    ! [B_53,A_54] :
      ( v1_relat_1(B_53)
      | ~ m1_subset_1(B_53,k1_zfmisc_1(A_54))
      | ~ v1_relat_1(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_83,plain,(
    ! [A_55,B_56] :
      ( v1_relat_1(A_55)
      | ~ v1_relat_1(B_56)
      | ~ r1_tarski(A_55,B_56) ) ),
    inference(resolution,[status(thm)],[c_32,c_78])).

tff(c_104,plain,(
    ! [B_62,A_63] :
      ( v1_relat_1(k1_setfam_1(B_62))
      | ~ v1_relat_1(A_63)
      | ~ r2_hidden(A_63,B_62) ) ),
    inference(resolution,[status(thm)],[c_34,c_83])).

tff(c_106,plain,(
    ! [A_6,D_11] :
      ( v1_relat_1(k1_setfam_1(k2_tarski(A_6,D_11)))
      | ~ v1_relat_1(D_11) ) ),
    inference(resolution,[status(thm)],[c_8,c_104])).

tff(c_110,plain,(
    ! [A_6,D_11] :
      ( v1_relat_1(k3_xboole_0(A_6,D_11))
      | ~ v1_relat_1(D_11) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_106])).

tff(c_46,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_66,plain,(
    ! [A_51,B_52] : k1_setfam_1(k2_tarski(A_51,B_52)) = k3_xboole_0(A_51,B_52) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_132,plain,(
    ! [A_72,B_73,A_74] :
      ( r1_tarski(k3_xboole_0(A_72,B_73),A_74)
      | ~ r2_hidden(A_74,k2_tarski(A_72,B_73)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_34])).

tff(c_139,plain,(
    ! [A_6,D_11] : r1_tarski(k3_xboole_0(A_6,D_11),D_11) ),
    inference(resolution,[status(thm)],[c_8,c_132])).

tff(c_38,plain,(
    ! [C_32,A_26,B_30] :
      ( r1_tarski(k5_relat_1(C_32,A_26),k5_relat_1(C_32,B_30))
      | ~ r1_tarski(A_26,B_30)
      | ~ v1_relat_1(C_32)
      | ~ v1_relat_1(B_30)
      | ~ v1_relat_1(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_44,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_2,plain,(
    ! [A_1,B_2] : r1_tarski(k3_xboole_0(A_1,B_2),A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_123,plain,(
    ! [A_69,B_70,C_71] :
      ( r1_tarski(A_69,k3_xboole_0(B_70,C_71))
      | ~ r1_tarski(A_69,C_71)
      | ~ r1_tarski(A_69,B_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_40,plain,(
    ~ r1_tarski(k5_relat_1('#skF_3',k3_xboole_0('#skF_4','#skF_5')),k3_xboole_0(k5_relat_1('#skF_3','#skF_4'),k5_relat_1('#skF_3','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_131,plain,
    ( ~ r1_tarski(k5_relat_1('#skF_3',k3_xboole_0('#skF_4','#skF_5')),k5_relat_1('#skF_3','#skF_5'))
    | ~ r1_tarski(k5_relat_1('#skF_3',k3_xboole_0('#skF_4','#skF_5')),k5_relat_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_123,c_40])).

tff(c_163,plain,(
    ~ r1_tarski(k5_relat_1('#skF_3',k3_xboole_0('#skF_4','#skF_5')),k5_relat_1('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_131])).

tff(c_166,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_4','#skF_5'),'#skF_4')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_4')
    | ~ v1_relat_1(k3_xboole_0('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_38,c_163])).

tff(c_169,plain,(
    ~ v1_relat_1(k3_xboole_0('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_46,c_2,c_166])).

tff(c_172,plain,(
    ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_110,c_169])).

tff(c_179,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_172])).

tff(c_180,plain,(
    ~ r1_tarski(k5_relat_1('#skF_3',k3_xboole_0('#skF_4','#skF_5')),k5_relat_1('#skF_3','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_131])).

tff(c_184,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_4','#skF_5'),'#skF_5')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_5')
    | ~ v1_relat_1(k3_xboole_0('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_38,c_180])).

tff(c_187,plain,(
    ~ v1_relat_1(k3_xboole_0('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_46,c_139,c_184])).

tff(c_190,plain,(
    ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_110,c_187])).

tff(c_197,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_190])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:01:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.06/1.26  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.06/1.27  
% 2.06/1.27  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.06/1.27  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > k2_enumset1 > k1_enumset1 > k5_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_setfam_1 > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4
% 2.06/1.27  
% 2.06/1.27  %Foreground sorts:
% 2.06/1.27  
% 2.06/1.27  
% 2.06/1.27  %Background operators:
% 2.06/1.27  
% 2.06/1.27  
% 2.06/1.27  %Foreground operators:
% 2.06/1.27  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.06/1.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.06/1.27  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.06/1.27  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.06/1.27  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.06/1.27  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.06/1.27  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.06/1.27  tff('#skF_5', type, '#skF_5': $i).
% 2.06/1.27  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.06/1.27  tff('#skF_3', type, '#skF_3': $i).
% 2.06/1.27  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.06/1.27  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.06/1.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.06/1.27  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.06/1.27  tff('#skF_4', type, '#skF_4': $i).
% 2.06/1.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.06/1.27  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.06/1.27  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.06/1.27  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.06/1.27  
% 2.06/1.29  tff(f_86, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => r1_tarski(k5_relat_1(A, k3_xboole_0(B, C)), k3_xboole_0(k5_relat_1(A, B), k5_relat_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_relat_1)).
% 2.06/1.29  tff(f_48, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 2.06/1.29  tff(f_42, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 2.06/1.29  tff(f_56, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(k1_setfam_1(B), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_setfam_1)).
% 2.06/1.29  tff(f_52, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 2.06/1.29  tff(f_63, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.06/1.29  tff(f_75, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (r1_tarski(A, B) => r1_tarski(k5_relat_1(C, A), k5_relat_1(C, B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_relat_1)).
% 2.06/1.29  tff(f_27, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 2.06/1.29  tff(f_33, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(A, C)) => r1_tarski(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_xboole_1)).
% 2.06/1.29  tff(c_42, plain, (v1_relat_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.06/1.29  tff(c_28, plain, (![A_17, B_18]: (k1_setfam_1(k2_tarski(A_17, B_18))=k3_xboole_0(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.06/1.29  tff(c_8, plain, (![D_11, A_6]: (r2_hidden(D_11, k2_tarski(A_6, D_11)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.06/1.29  tff(c_34, plain, (![B_22, A_21]: (r1_tarski(k1_setfam_1(B_22), A_21) | ~r2_hidden(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.06/1.29  tff(c_32, plain, (![A_19, B_20]: (m1_subset_1(A_19, k1_zfmisc_1(B_20)) | ~r1_tarski(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.06/1.29  tff(c_78, plain, (![B_53, A_54]: (v1_relat_1(B_53) | ~m1_subset_1(B_53, k1_zfmisc_1(A_54)) | ~v1_relat_1(A_54))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.06/1.29  tff(c_83, plain, (![A_55, B_56]: (v1_relat_1(A_55) | ~v1_relat_1(B_56) | ~r1_tarski(A_55, B_56))), inference(resolution, [status(thm)], [c_32, c_78])).
% 2.06/1.29  tff(c_104, plain, (![B_62, A_63]: (v1_relat_1(k1_setfam_1(B_62)) | ~v1_relat_1(A_63) | ~r2_hidden(A_63, B_62))), inference(resolution, [status(thm)], [c_34, c_83])).
% 2.06/1.29  tff(c_106, plain, (![A_6, D_11]: (v1_relat_1(k1_setfam_1(k2_tarski(A_6, D_11))) | ~v1_relat_1(D_11))), inference(resolution, [status(thm)], [c_8, c_104])).
% 2.06/1.29  tff(c_110, plain, (![A_6, D_11]: (v1_relat_1(k3_xboole_0(A_6, D_11)) | ~v1_relat_1(D_11))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_106])).
% 2.06/1.29  tff(c_46, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.06/1.29  tff(c_66, plain, (![A_51, B_52]: (k1_setfam_1(k2_tarski(A_51, B_52))=k3_xboole_0(A_51, B_52))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.06/1.29  tff(c_132, plain, (![A_72, B_73, A_74]: (r1_tarski(k3_xboole_0(A_72, B_73), A_74) | ~r2_hidden(A_74, k2_tarski(A_72, B_73)))), inference(superposition, [status(thm), theory('equality')], [c_66, c_34])).
% 2.06/1.29  tff(c_139, plain, (![A_6, D_11]: (r1_tarski(k3_xboole_0(A_6, D_11), D_11))), inference(resolution, [status(thm)], [c_8, c_132])).
% 2.06/1.29  tff(c_38, plain, (![C_32, A_26, B_30]: (r1_tarski(k5_relat_1(C_32, A_26), k5_relat_1(C_32, B_30)) | ~r1_tarski(A_26, B_30) | ~v1_relat_1(C_32) | ~v1_relat_1(B_30) | ~v1_relat_1(A_26))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.06/1.29  tff(c_44, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.06/1.29  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(k3_xboole_0(A_1, B_2), A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.06/1.29  tff(c_123, plain, (![A_69, B_70, C_71]: (r1_tarski(A_69, k3_xboole_0(B_70, C_71)) | ~r1_tarski(A_69, C_71) | ~r1_tarski(A_69, B_70))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.06/1.29  tff(c_40, plain, (~r1_tarski(k5_relat_1('#skF_3', k3_xboole_0('#skF_4', '#skF_5')), k3_xboole_0(k5_relat_1('#skF_3', '#skF_4'), k5_relat_1('#skF_3', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.06/1.29  tff(c_131, plain, (~r1_tarski(k5_relat_1('#skF_3', k3_xboole_0('#skF_4', '#skF_5')), k5_relat_1('#skF_3', '#skF_5')) | ~r1_tarski(k5_relat_1('#skF_3', k3_xboole_0('#skF_4', '#skF_5')), k5_relat_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_123, c_40])).
% 2.06/1.29  tff(c_163, plain, (~r1_tarski(k5_relat_1('#skF_3', k3_xboole_0('#skF_4', '#skF_5')), k5_relat_1('#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_131])).
% 2.06/1.29  tff(c_166, plain, (~r1_tarski(k3_xboole_0('#skF_4', '#skF_5'), '#skF_4') | ~v1_relat_1('#skF_3') | ~v1_relat_1('#skF_4') | ~v1_relat_1(k3_xboole_0('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_38, c_163])).
% 2.06/1.29  tff(c_169, plain, (~v1_relat_1(k3_xboole_0('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_46, c_2, c_166])).
% 2.06/1.29  tff(c_172, plain, (~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_110, c_169])).
% 2.06/1.29  tff(c_179, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_172])).
% 2.06/1.29  tff(c_180, plain, (~r1_tarski(k5_relat_1('#skF_3', k3_xboole_0('#skF_4', '#skF_5')), k5_relat_1('#skF_3', '#skF_5'))), inference(splitRight, [status(thm)], [c_131])).
% 2.06/1.29  tff(c_184, plain, (~r1_tarski(k3_xboole_0('#skF_4', '#skF_5'), '#skF_5') | ~v1_relat_1('#skF_3') | ~v1_relat_1('#skF_5') | ~v1_relat_1(k3_xboole_0('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_38, c_180])).
% 2.06/1.29  tff(c_187, plain, (~v1_relat_1(k3_xboole_0('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_46, c_139, c_184])).
% 2.06/1.29  tff(c_190, plain, (~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_110, c_187])).
% 2.06/1.29  tff(c_197, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_190])).
% 2.06/1.29  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.06/1.29  
% 2.06/1.29  Inference rules
% 2.06/1.29  ----------------------
% 2.06/1.29  #Ref     : 0
% 2.06/1.29  #Sup     : 29
% 2.06/1.29  #Fact    : 0
% 2.06/1.29  #Define  : 0
% 2.06/1.29  #Split   : 1
% 2.06/1.29  #Chain   : 0
% 2.06/1.29  #Close   : 0
% 2.06/1.29  
% 2.06/1.29  Ordering : KBO
% 2.06/1.29  
% 2.06/1.29  Simplification rules
% 2.06/1.29  ----------------------
% 2.06/1.29  #Subsume      : 4
% 2.06/1.29  #Demod        : 11
% 2.06/1.29  #Tautology    : 10
% 2.06/1.29  #SimpNegUnit  : 0
% 2.06/1.29  #BackRed      : 0
% 2.06/1.29  
% 2.06/1.29  #Partial instantiations: 0
% 2.06/1.29  #Strategies tried      : 1
% 2.06/1.29  
% 2.06/1.29  Timing (in seconds)
% 2.06/1.29  ----------------------
% 2.06/1.29  Preprocessing        : 0.32
% 2.06/1.29  Parsing              : 0.17
% 2.06/1.29  CNF conversion       : 0.02
% 2.06/1.29  Main loop            : 0.17
% 2.06/1.29  Inferencing          : 0.06
% 2.06/1.29  Reduction            : 0.05
% 2.06/1.29  Demodulation         : 0.04
% 2.06/1.29  BG Simplification    : 0.01
% 2.06/1.29  Subsumption          : 0.03
% 2.06/1.29  Abstraction          : 0.01
% 2.06/1.29  MUC search           : 0.00
% 2.06/1.29  Cooper               : 0.00
% 2.06/1.29  Total                : 0.52
% 2.06/1.29  Index Insertion      : 0.00
% 2.06/1.29  Index Deletion       : 0.00
% 2.06/1.29  Index Matching       : 0.00
% 2.06/1.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------
