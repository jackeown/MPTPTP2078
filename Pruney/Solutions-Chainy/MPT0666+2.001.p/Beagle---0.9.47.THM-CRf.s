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
% DateTime   : Thu Dec  3 10:04:17 EST 2020

% Result     : Theorem 2.69s
% Output     : CNFRefutation 2.69s
% Verified   : 
% Statistics : Number of formulae       :   44 (  52 expanded)
%              Number of leaves         :   22 (  27 expanded)
%              Depth                    :    8
%              Number of atoms          :   58 (  87 expanded)
%              Number of equality atoms :   17 (  29 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > v1_funct_1 > k7_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_68,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => ( r1_tarski(A,B)
         => ( k7_relat_1(k7_relat_1(C,A),B) = k7_relat_1(C,A)
            & k7_relat_1(k7_relat_1(C,B),A) = k7_relat_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t82_funct_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(A,B)
       => k7_relat_1(k7_relat_1(C,B),A) = k7_relat_1(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t103_relat_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k3_xboole_0(B,C))
     => r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_xboole_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).

tff(c_24,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_20,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_1024,plain,(
    ! [C_102,B_103,A_104] :
      ( k7_relat_1(k7_relat_1(C_102,B_103),A_104) = k7_relat_1(C_102,A_104)
      | ~ r1_tarski(A_104,B_103)
      | ~ v1_relat_1(C_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_10,plain,(
    ! [A_10,B_11] :
      ( v1_relat_1(k7_relat_1(A_10,B_11))
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_68,plain,(
    ! [A_25,B_26] :
      ( k3_xboole_0(A_25,B_26) = A_25
      | ~ r1_tarski(A_25,B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_72,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_20,c_68])).

tff(c_14,plain,(
    ! [B_16,A_15] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_16,A_15)),A_15)
      | ~ v1_relat_1(B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_77,plain,(
    ! [A_27,B_28,C_29] :
      ( r1_tarski(A_27,B_28)
      | ~ r1_tarski(A_27,k3_xboole_0(B_28,C_29)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_99,plain,(
    ! [A_32,B_33,A_34] :
      ( r1_tarski(A_32,B_33)
      | ~ r1_tarski(A_32,k3_xboole_0(A_34,B_33)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_77])).

tff(c_171,plain,(
    ! [B_42,A_43,B_44] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_42,k3_xboole_0(A_43,B_44))),B_44)
      | ~ v1_relat_1(B_42) ) ),
    inference(resolution,[status(thm)],[c_14,c_99])).

tff(c_206,plain,(
    ! [B_45] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_45,'#skF_1')),'#skF_2')
      | ~ v1_relat_1(B_45) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_171])).

tff(c_16,plain,(
    ! [B_18,A_17] :
      ( k7_relat_1(B_18,A_17) = B_18
      | ~ r1_tarski(k1_relat_1(B_18),A_17)
      | ~ v1_relat_1(B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_818,plain,(
    ! [B_88] :
      ( k7_relat_1(k7_relat_1(B_88,'#skF_1'),'#skF_2') = k7_relat_1(B_88,'#skF_1')
      | ~ v1_relat_1(k7_relat_1(B_88,'#skF_1'))
      | ~ v1_relat_1(B_88) ) ),
    inference(resolution,[status(thm)],[c_206,c_16])).

tff(c_832,plain,(
    ! [A_89] :
      ( k7_relat_1(k7_relat_1(A_89,'#skF_1'),'#skF_2') = k7_relat_1(A_89,'#skF_1')
      | ~ v1_relat_1(A_89) ) ),
    inference(resolution,[status(thm)],[c_10,c_818])).

tff(c_18,plain,
    ( k7_relat_1(k7_relat_1('#skF_3','#skF_2'),'#skF_1') != k7_relat_1('#skF_3','#skF_1')
    | k7_relat_1(k7_relat_1('#skF_3','#skF_1'),'#skF_2') != k7_relat_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_87,plain,(
    k7_relat_1(k7_relat_1('#skF_3','#skF_1'),'#skF_2') != k7_relat_1('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_18])).

tff(c_855,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_832,c_87])).

tff(c_883,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_855])).

tff(c_884,plain,(
    k7_relat_1(k7_relat_1('#skF_3','#skF_2'),'#skF_1') != k7_relat_1('#skF_3','#skF_1') ),
    inference(splitRight,[status(thm)],[c_18])).

tff(c_1037,plain,
    ( ~ r1_tarski('#skF_1','#skF_2')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1024,c_884])).

tff(c_1063,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_20,c_1037])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n001.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 17:53:30 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.69/1.42  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.69/1.42  
% 2.69/1.42  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.69/1.42  %$ r1_tarski > v1_relat_1 > v1_funct_1 > k7_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 2.69/1.42  
% 2.69/1.42  %Foreground sorts:
% 2.69/1.42  
% 2.69/1.42  
% 2.69/1.42  %Background operators:
% 2.69/1.42  
% 2.69/1.42  
% 2.69/1.42  %Foreground operators:
% 2.69/1.42  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.69/1.42  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.69/1.42  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.69/1.42  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.69/1.42  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.69/1.42  tff('#skF_2', type, '#skF_2': $i).
% 2.69/1.42  tff('#skF_3', type, '#skF_3': $i).
% 2.69/1.42  tff('#skF_1', type, '#skF_1': $i).
% 2.69/1.42  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.69/1.42  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.69/1.42  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.69/1.42  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.69/1.42  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.69/1.42  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.69/1.42  
% 2.69/1.43  tff(f_68, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r1_tarski(A, B) => ((k7_relat_1(k7_relat_1(C, A), B) = k7_relat_1(C, A)) & (k7_relat_1(k7_relat_1(C, B), A) = k7_relat_1(C, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t82_funct_1)).
% 2.69/1.43  tff(f_47, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => (k7_relat_1(k7_relat_1(C, B), A) = k7_relat_1(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t103_relat_1)).
% 2.69/1.43  tff(f_41, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 2.69/1.43  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.69/1.43  tff(f_51, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_relat_1)).
% 2.69/1.43  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.69/1.43  tff(f_31, axiom, (![A, B, C]: (r1_tarski(A, k3_xboole_0(B, C)) => r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_xboole_1)).
% 2.69/1.43  tff(f_57, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t97_relat_1)).
% 2.69/1.43  tff(c_24, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.69/1.43  tff(c_20, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.69/1.43  tff(c_1024, plain, (![C_102, B_103, A_104]: (k7_relat_1(k7_relat_1(C_102, B_103), A_104)=k7_relat_1(C_102, A_104) | ~r1_tarski(A_104, B_103) | ~v1_relat_1(C_102))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.69/1.43  tff(c_10, plain, (![A_10, B_11]: (v1_relat_1(k7_relat_1(A_10, B_11)) | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.69/1.43  tff(c_68, plain, (![A_25, B_26]: (k3_xboole_0(A_25, B_26)=A_25 | ~r1_tarski(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.69/1.43  tff(c_72, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(resolution, [status(thm)], [c_20, c_68])).
% 2.69/1.43  tff(c_14, plain, (![B_16, A_15]: (r1_tarski(k1_relat_1(k7_relat_1(B_16, A_15)), A_15) | ~v1_relat_1(B_16))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.69/1.43  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.69/1.43  tff(c_77, plain, (![A_27, B_28, C_29]: (r1_tarski(A_27, B_28) | ~r1_tarski(A_27, k3_xboole_0(B_28, C_29)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.69/1.43  tff(c_99, plain, (![A_32, B_33, A_34]: (r1_tarski(A_32, B_33) | ~r1_tarski(A_32, k3_xboole_0(A_34, B_33)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_77])).
% 2.69/1.43  tff(c_171, plain, (![B_42, A_43, B_44]: (r1_tarski(k1_relat_1(k7_relat_1(B_42, k3_xboole_0(A_43, B_44))), B_44) | ~v1_relat_1(B_42))), inference(resolution, [status(thm)], [c_14, c_99])).
% 2.69/1.43  tff(c_206, plain, (![B_45]: (r1_tarski(k1_relat_1(k7_relat_1(B_45, '#skF_1')), '#skF_2') | ~v1_relat_1(B_45))), inference(superposition, [status(thm), theory('equality')], [c_72, c_171])).
% 2.69/1.43  tff(c_16, plain, (![B_18, A_17]: (k7_relat_1(B_18, A_17)=B_18 | ~r1_tarski(k1_relat_1(B_18), A_17) | ~v1_relat_1(B_18))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.69/1.43  tff(c_818, plain, (![B_88]: (k7_relat_1(k7_relat_1(B_88, '#skF_1'), '#skF_2')=k7_relat_1(B_88, '#skF_1') | ~v1_relat_1(k7_relat_1(B_88, '#skF_1')) | ~v1_relat_1(B_88))), inference(resolution, [status(thm)], [c_206, c_16])).
% 2.69/1.43  tff(c_832, plain, (![A_89]: (k7_relat_1(k7_relat_1(A_89, '#skF_1'), '#skF_2')=k7_relat_1(A_89, '#skF_1') | ~v1_relat_1(A_89))), inference(resolution, [status(thm)], [c_10, c_818])).
% 2.69/1.43  tff(c_18, plain, (k7_relat_1(k7_relat_1('#skF_3', '#skF_2'), '#skF_1')!=k7_relat_1('#skF_3', '#skF_1') | k7_relat_1(k7_relat_1('#skF_3', '#skF_1'), '#skF_2')!=k7_relat_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.69/1.43  tff(c_87, plain, (k7_relat_1(k7_relat_1('#skF_3', '#skF_1'), '#skF_2')!=k7_relat_1('#skF_3', '#skF_1')), inference(splitLeft, [status(thm)], [c_18])).
% 2.69/1.43  tff(c_855, plain, (~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_832, c_87])).
% 2.69/1.43  tff(c_883, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_855])).
% 2.69/1.43  tff(c_884, plain, (k7_relat_1(k7_relat_1('#skF_3', '#skF_2'), '#skF_1')!=k7_relat_1('#skF_3', '#skF_1')), inference(splitRight, [status(thm)], [c_18])).
% 2.69/1.43  tff(c_1037, plain, (~r1_tarski('#skF_1', '#skF_2') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1024, c_884])).
% 2.69/1.43  tff(c_1063, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_20, c_1037])).
% 2.69/1.43  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.69/1.43  
% 2.69/1.43  Inference rules
% 2.69/1.43  ----------------------
% 2.69/1.43  #Ref     : 0
% 2.69/1.43  #Sup     : 253
% 2.69/1.43  #Fact    : 0
% 2.69/1.43  #Define  : 0
% 2.69/1.43  #Split   : 3
% 2.69/1.43  #Chain   : 0
% 2.69/1.43  #Close   : 0
% 2.69/1.43  
% 2.69/1.43  Ordering : KBO
% 2.69/1.43  
% 2.69/1.43  Simplification rules
% 2.69/1.43  ----------------------
% 2.69/1.43  #Subsume      : 79
% 2.69/1.43  #Demod        : 29
% 2.69/1.43  #Tautology    : 39
% 2.69/1.43  #SimpNegUnit  : 0
% 2.69/1.43  #BackRed      : 0
% 2.69/1.43  
% 2.69/1.43  #Partial instantiations: 0
% 2.69/1.43  #Strategies tried      : 1
% 2.69/1.43  
% 2.69/1.43  Timing (in seconds)
% 2.69/1.43  ----------------------
% 2.69/1.44  Preprocessing        : 0.27
% 2.69/1.44  Parsing              : 0.15
% 2.69/1.44  CNF conversion       : 0.02
% 2.69/1.44  Main loop            : 0.41
% 2.69/1.44  Inferencing          : 0.16
% 2.69/1.44  Reduction            : 0.12
% 2.69/1.44  Demodulation         : 0.09
% 2.69/1.44  BG Simplification    : 0.02
% 2.69/1.44  Subsumption          : 0.08
% 2.69/1.44  Abstraction          : 0.02
% 2.69/1.44  MUC search           : 0.00
% 2.69/1.44  Cooper               : 0.00
% 2.69/1.44  Total                : 0.71
% 2.69/1.44  Index Insertion      : 0.00
% 2.69/1.44  Index Deletion       : 0.00
% 2.69/1.44  Index Matching       : 0.00
% 2.69/1.44  BG Taut test         : 0.00
%------------------------------------------------------------------------------
