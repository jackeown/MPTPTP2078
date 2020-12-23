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
% DateTime   : Thu Dec  3 09:58:21 EST 2020

% Result     : Theorem 1.94s
% Output     : CNFRefutation 2.08s
% Verified   : 
% Statistics : Number of formulae       :   59 (  91 expanded)
%              Number of leaves         :   30 (  45 expanded)
%              Depth                    :    7
%              Number of atoms          :   74 ( 150 expanded)
%              Number of equality atoms :    6 (  15 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_setfam_1 > k1_relat_1 > #skF_1 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_86,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => r1_tarski(k2_relat_1(k3_xboole_0(A,B)),k3_xboole_0(k2_relat_1(A),k2_relat_1(B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_relat_1)).

tff(f_52,axiom,(
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

tff(f_60,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(k1_setfam_1(B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_setfam_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_67,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_78,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(A,B)
           => ( r1_tarski(k1_relat_1(A),k1_relat_1(B))
              & r1_tarski(k2_relat_1(A),k2_relat_1(B)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C) )
     => r1_tarski(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).

tff(c_48,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_32,plain,(
    ! [A_26,B_27] : k1_setfam_1(k2_tarski(A_26,B_27)) = k3_xboole_0(A_26,B_27) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_8,plain,(
    ! [D_11,A_6] : r2_hidden(D_11,k2_tarski(A_6,D_11)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_38,plain,(
    ! [B_31,A_30] :
      ( r1_tarski(k1_setfam_1(B_31),A_30)
      | ~ r2_hidden(A_30,B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_36,plain,(
    ! [A_28,B_29] :
      ( m1_subset_1(A_28,k1_zfmisc_1(B_29))
      | ~ r1_tarski(A_28,B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_82,plain,(
    ! [B_55,A_56] :
      ( v1_relat_1(B_55)
      | ~ m1_subset_1(B_55,k1_zfmisc_1(A_56))
      | ~ v1_relat_1(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_87,plain,(
    ! [A_57,B_58] :
      ( v1_relat_1(A_57)
      | ~ v1_relat_1(B_58)
      | ~ r1_tarski(A_57,B_58) ) ),
    inference(resolution,[status(thm)],[c_36,c_82])).

tff(c_97,plain,(
    ! [B_61,A_62] :
      ( v1_relat_1(k1_setfam_1(B_61))
      | ~ v1_relat_1(A_62)
      | ~ r2_hidden(A_62,B_61) ) ),
    inference(resolution,[status(thm)],[c_38,c_87])).

tff(c_99,plain,(
    ! [A_6,D_11] :
      ( v1_relat_1(k1_setfam_1(k2_tarski(A_6,D_11)))
      | ~ v1_relat_1(D_11) ) ),
    inference(resolution,[status(thm)],[c_8,c_97])).

tff(c_103,plain,(
    ! [A_6,D_11] :
      ( v1_relat_1(k3_xboole_0(A_6,D_11))
      | ~ v1_relat_1(D_11) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_99])).

tff(c_65,plain,(
    ! [A_51,B_52] : k1_setfam_1(k2_tarski(A_51,B_52)) = k3_xboole_0(A_51,B_52) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_127,plain,(
    ! [A_71,B_72,A_73] :
      ( r1_tarski(k3_xboole_0(A_71,B_72),A_73)
      | ~ r2_hidden(A_73,k2_tarski(A_71,B_72)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_65,c_38])).

tff(c_134,plain,(
    ! [A_6,D_11] : r1_tarski(k3_xboole_0(A_6,D_11),D_11) ),
    inference(resolution,[status(thm)],[c_8,c_127])).

tff(c_42,plain,(
    ! [A_35,B_37] :
      ( r1_tarski(k2_relat_1(A_35),k2_relat_1(B_37))
      | ~ r1_tarski(A_35,B_37)
      | ~ v1_relat_1(B_37)
      | ~ v1_relat_1(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_50,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_2,plain,(
    ! [A_1,B_2] : r1_tarski(k3_xboole_0(A_1,B_2),A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_151,plain,(
    ! [A_80,B_81,C_82] :
      ( r1_tarski(A_80,k3_xboole_0(B_81,C_82))
      | ~ r1_tarski(A_80,C_82)
      | ~ r1_tarski(A_80,B_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_46,plain,(
    ~ r1_tarski(k2_relat_1(k3_xboole_0('#skF_3','#skF_4')),k3_xboole_0(k2_relat_1('#skF_3'),k2_relat_1('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_159,plain,
    ( ~ r1_tarski(k2_relat_1(k3_xboole_0('#skF_3','#skF_4')),k2_relat_1('#skF_4'))
    | ~ r1_tarski(k2_relat_1(k3_xboole_0('#skF_3','#skF_4')),k2_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_151,c_46])).

tff(c_188,plain,(
    ~ r1_tarski(k2_relat_1(k3_xboole_0('#skF_3','#skF_4')),k2_relat_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_159])).

tff(c_191,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_3','#skF_4'),'#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1(k3_xboole_0('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_42,c_188])).

tff(c_194,plain,(
    ~ v1_relat_1(k3_xboole_0('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_2,c_191])).

tff(c_197,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_103,c_194])).

tff(c_204,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_197])).

tff(c_205,plain,(
    ~ r1_tarski(k2_relat_1(k3_xboole_0('#skF_3','#skF_4')),k2_relat_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_159])).

tff(c_209,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_3','#skF_4'),'#skF_4')
    | ~ v1_relat_1('#skF_4')
    | ~ v1_relat_1(k3_xboole_0('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_42,c_205])).

tff(c_212,plain,(
    ~ v1_relat_1(k3_xboole_0('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_134,c_209])).

tff(c_215,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_103,c_212])).

tff(c_222,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_215])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:23:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.94/1.22  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.94/1.23  
% 1.94/1.23  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.08/1.23  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_setfam_1 > k1_relat_1 > #skF_1 > #skF_3 > #skF_2 > #skF_4
% 2.08/1.23  
% 2.08/1.23  %Foreground sorts:
% 2.08/1.23  
% 2.08/1.23  
% 2.08/1.23  %Background operators:
% 2.08/1.23  
% 2.08/1.23  
% 2.08/1.23  %Foreground operators:
% 2.08/1.23  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.08/1.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.08/1.23  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.08/1.23  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.08/1.23  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.08/1.23  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.08/1.23  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.08/1.23  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.08/1.23  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.08/1.23  tff('#skF_3', type, '#skF_3': $i).
% 2.08/1.23  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.08/1.23  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.08/1.23  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.08/1.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.08/1.23  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.08/1.23  tff('#skF_4', type, '#skF_4': $i).
% 2.08/1.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.08/1.23  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.08/1.23  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.08/1.23  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.08/1.23  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.08/1.23  
% 2.08/1.24  tff(f_86, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k3_xboole_0(A, B)), k3_xboole_0(k2_relat_1(A), k2_relat_1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t27_relat_1)).
% 2.08/1.24  tff(f_52, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 2.08/1.24  tff(f_42, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 2.08/1.24  tff(f_60, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(k1_setfam_1(B), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_setfam_1)).
% 2.08/1.24  tff(f_56, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 2.08/1.24  tff(f_67, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.08/1.24  tff(f_78, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => (r1_tarski(k1_relat_1(A), k1_relat_1(B)) & r1_tarski(k2_relat_1(A), k2_relat_1(B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_relat_1)).
% 2.08/1.24  tff(f_27, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 2.08/1.24  tff(f_33, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(A, C)) => r1_tarski(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_xboole_1)).
% 2.08/1.24  tff(c_48, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.08/1.24  tff(c_32, plain, (![A_26, B_27]: (k1_setfam_1(k2_tarski(A_26, B_27))=k3_xboole_0(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.08/1.24  tff(c_8, plain, (![D_11, A_6]: (r2_hidden(D_11, k2_tarski(A_6, D_11)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.08/1.24  tff(c_38, plain, (![B_31, A_30]: (r1_tarski(k1_setfam_1(B_31), A_30) | ~r2_hidden(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.08/1.24  tff(c_36, plain, (![A_28, B_29]: (m1_subset_1(A_28, k1_zfmisc_1(B_29)) | ~r1_tarski(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.08/1.24  tff(c_82, plain, (![B_55, A_56]: (v1_relat_1(B_55) | ~m1_subset_1(B_55, k1_zfmisc_1(A_56)) | ~v1_relat_1(A_56))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.08/1.24  tff(c_87, plain, (![A_57, B_58]: (v1_relat_1(A_57) | ~v1_relat_1(B_58) | ~r1_tarski(A_57, B_58))), inference(resolution, [status(thm)], [c_36, c_82])).
% 2.08/1.24  tff(c_97, plain, (![B_61, A_62]: (v1_relat_1(k1_setfam_1(B_61)) | ~v1_relat_1(A_62) | ~r2_hidden(A_62, B_61))), inference(resolution, [status(thm)], [c_38, c_87])).
% 2.08/1.24  tff(c_99, plain, (![A_6, D_11]: (v1_relat_1(k1_setfam_1(k2_tarski(A_6, D_11))) | ~v1_relat_1(D_11))), inference(resolution, [status(thm)], [c_8, c_97])).
% 2.08/1.24  tff(c_103, plain, (![A_6, D_11]: (v1_relat_1(k3_xboole_0(A_6, D_11)) | ~v1_relat_1(D_11))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_99])).
% 2.08/1.24  tff(c_65, plain, (![A_51, B_52]: (k1_setfam_1(k2_tarski(A_51, B_52))=k3_xboole_0(A_51, B_52))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.08/1.24  tff(c_127, plain, (![A_71, B_72, A_73]: (r1_tarski(k3_xboole_0(A_71, B_72), A_73) | ~r2_hidden(A_73, k2_tarski(A_71, B_72)))), inference(superposition, [status(thm), theory('equality')], [c_65, c_38])).
% 2.08/1.24  tff(c_134, plain, (![A_6, D_11]: (r1_tarski(k3_xboole_0(A_6, D_11), D_11))), inference(resolution, [status(thm)], [c_8, c_127])).
% 2.08/1.24  tff(c_42, plain, (![A_35, B_37]: (r1_tarski(k2_relat_1(A_35), k2_relat_1(B_37)) | ~r1_tarski(A_35, B_37) | ~v1_relat_1(B_37) | ~v1_relat_1(A_35))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.08/1.24  tff(c_50, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.08/1.24  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(k3_xboole_0(A_1, B_2), A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.08/1.24  tff(c_151, plain, (![A_80, B_81, C_82]: (r1_tarski(A_80, k3_xboole_0(B_81, C_82)) | ~r1_tarski(A_80, C_82) | ~r1_tarski(A_80, B_81))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.08/1.24  tff(c_46, plain, (~r1_tarski(k2_relat_1(k3_xboole_0('#skF_3', '#skF_4')), k3_xboole_0(k2_relat_1('#skF_3'), k2_relat_1('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.08/1.24  tff(c_159, plain, (~r1_tarski(k2_relat_1(k3_xboole_0('#skF_3', '#skF_4')), k2_relat_1('#skF_4')) | ~r1_tarski(k2_relat_1(k3_xboole_0('#skF_3', '#skF_4')), k2_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_151, c_46])).
% 2.08/1.24  tff(c_188, plain, (~r1_tarski(k2_relat_1(k3_xboole_0('#skF_3', '#skF_4')), k2_relat_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_159])).
% 2.08/1.24  tff(c_191, plain, (~r1_tarski(k3_xboole_0('#skF_3', '#skF_4'), '#skF_3') | ~v1_relat_1('#skF_3') | ~v1_relat_1(k3_xboole_0('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_42, c_188])).
% 2.08/1.24  tff(c_194, plain, (~v1_relat_1(k3_xboole_0('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_2, c_191])).
% 2.08/1.24  tff(c_197, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_103, c_194])).
% 2.08/1.24  tff(c_204, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_197])).
% 2.08/1.24  tff(c_205, plain, (~r1_tarski(k2_relat_1(k3_xboole_0('#skF_3', '#skF_4')), k2_relat_1('#skF_4'))), inference(splitRight, [status(thm)], [c_159])).
% 2.08/1.24  tff(c_209, plain, (~r1_tarski(k3_xboole_0('#skF_3', '#skF_4'), '#skF_4') | ~v1_relat_1('#skF_4') | ~v1_relat_1(k3_xboole_0('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_42, c_205])).
% 2.08/1.24  tff(c_212, plain, (~v1_relat_1(k3_xboole_0('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_134, c_209])).
% 2.08/1.24  tff(c_215, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_103, c_212])).
% 2.08/1.24  tff(c_222, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_215])).
% 2.08/1.24  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.08/1.24  
% 2.08/1.24  Inference rules
% 2.08/1.24  ----------------------
% 2.08/1.24  #Ref     : 0
% 2.08/1.24  #Sup     : 34
% 2.08/1.24  #Fact    : 0
% 2.08/1.24  #Define  : 0
% 2.08/1.24  #Split   : 1
% 2.08/1.24  #Chain   : 0
% 2.08/1.24  #Close   : 0
% 2.08/1.24  
% 2.08/1.24  Ordering : KBO
% 2.08/1.24  
% 2.08/1.24  Simplification rules
% 2.08/1.24  ----------------------
% 2.08/1.24  #Subsume      : 4
% 2.08/1.25  #Demod        : 9
% 2.08/1.25  #Tautology    : 14
% 2.08/1.25  #SimpNegUnit  : 0
% 2.08/1.25  #BackRed      : 0
% 2.08/1.25  
% 2.08/1.25  #Partial instantiations: 0
% 2.08/1.25  #Strategies tried      : 1
% 2.08/1.25  
% 2.08/1.25  Timing (in seconds)
% 2.08/1.25  ----------------------
% 2.15/1.25  Preprocessing        : 0.31
% 2.15/1.25  Parsing              : 0.16
% 2.15/1.25  CNF conversion       : 0.02
% 2.15/1.25  Main loop            : 0.17
% 2.15/1.25  Inferencing          : 0.07
% 2.15/1.25  Reduction            : 0.05
% 2.15/1.25  Demodulation         : 0.04
% 2.15/1.25  BG Simplification    : 0.01
% 2.15/1.25  Subsumption          : 0.03
% 2.15/1.25  Abstraction          : 0.01
% 2.15/1.25  MUC search           : 0.00
% 2.15/1.25  Cooper               : 0.00
% 2.15/1.25  Total                : 0.51
% 2.15/1.25  Index Insertion      : 0.00
% 2.15/1.25  Index Deletion       : 0.00
% 2.15/1.25  Index Matching       : 0.00
% 2.15/1.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------
