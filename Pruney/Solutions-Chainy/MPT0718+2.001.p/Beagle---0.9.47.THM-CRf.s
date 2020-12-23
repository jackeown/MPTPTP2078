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
% DateTime   : Thu Dec  3 10:05:41 EST 2020

% Result     : Theorem 2.06s
% Output     : CNFRefutation 2.06s
% Verified   : 
% Statistics : Number of formulae       :   56 (  63 expanded)
%              Number of leaves         :   29 (  36 expanded)
%              Depth                    :    9
%              Number of atoms          :  110 ( 157 expanded)
%              Number of equality atoms :   13 (  19 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_funct_1 > r2_hidden > v2_relat_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_tarski > k1_funct_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(v2_relat_1,type,(
    v2_relat_1: $i > $o )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(v5_funct_1,type,(
    v5_funct_1: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_92,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ! [B] :
            ( ( v1_relat_1(B)
              & v1_funct_1(B) )
           => ( ( v5_funct_1(A,B)
                & k1_relat_1(A) = k1_relat_1(B) )
             => v2_relat_1(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t173_funct_1)).

tff(f_53,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_relat_1(A)
      <=> ! [B] :
            ~ ( r2_hidden(B,k1_relat_1(A))
              & v1_xboole_0(k1_funct_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d15_funct_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_36,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_38,axiom,(
    ! [A] : k10_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t172_relat_1)).

tff(f_41,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_76,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r2_hidden(A,k2_relat_1(B))
      <=> k10_relat_1(B,k1_tarski(A)) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t142_funct_1)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_69,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( v5_funct_1(B,A)
          <=> ! [C] :
                ( r2_hidden(C,k1_relat_1(B))
               => r2_hidden(k1_funct_1(B,C),k1_funct_1(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d20_funct_1)).

tff(c_32,plain,(
    ~ v2_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_40,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_38,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_36,plain,(
    v5_funct_1('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_20,plain,(
    ! [A_5] :
      ( r2_hidden('#skF_1'(A_5),k1_relat_1(A_5))
      | v2_relat_1(A_5)
      | ~ v1_funct_1(A_5)
      | ~ v1_relat_1(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_44,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_42,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_34,plain,(
    k1_relat_1('#skF_3') = k1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_57,plain,(
    ! [A_22] :
      ( v1_relat_1(A_22)
      | ~ v1_xboole_0(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_61,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_57])).

tff(c_10,plain,(
    ! [A_4] : k10_relat_1(k1_xboole_0,A_4) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_12,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_84,plain,(
    ! [B_26,A_27] :
      ( k10_relat_1(B_26,k1_tarski(A_27)) != k1_xboole_0
      | ~ r2_hidden(A_27,k2_relat_1(B_26))
      | ~ v1_relat_1(B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_87,plain,(
    ! [A_27] :
      ( k10_relat_1(k1_xboole_0,k1_tarski(A_27)) != k1_xboole_0
      | ~ r2_hidden(A_27,k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_84])).

tff(c_89,plain,(
    ! [A_27] : ~ r2_hidden(A_27,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_10,c_87])).

tff(c_102,plain,(
    ! [A_31] :
      ( v1_xboole_0(k1_funct_1(A_31,'#skF_1'(A_31)))
      | v2_relat_1(A_31)
      | ~ v1_funct_1(A_31)
      | ~ v1_relat_1(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_109,plain,(
    ! [A_31] :
      ( k1_funct_1(A_31,'#skF_1'(A_31)) = k1_xboole_0
      | v2_relat_1(A_31)
      | ~ v1_funct_1(A_31)
      | ~ v1_relat_1(A_31) ) ),
    inference(resolution,[status(thm)],[c_102,c_4])).

tff(c_204,plain,(
    ! [B_45,C_46,A_47] :
      ( r2_hidden(k1_funct_1(B_45,C_46),k1_funct_1(A_47,C_46))
      | ~ r2_hidden(C_46,k1_relat_1(B_45))
      | ~ v5_funct_1(B_45,A_47)
      | ~ v1_funct_1(B_45)
      | ~ v1_relat_1(B_45)
      | ~ v1_funct_1(A_47)
      | ~ v1_relat_1(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_210,plain,(
    ! [B_45,A_31] :
      ( r2_hidden(k1_funct_1(B_45,'#skF_1'(A_31)),k1_xboole_0)
      | ~ r2_hidden('#skF_1'(A_31),k1_relat_1(B_45))
      | ~ v5_funct_1(B_45,A_31)
      | ~ v1_funct_1(B_45)
      | ~ v1_relat_1(B_45)
      | ~ v1_funct_1(A_31)
      | ~ v1_relat_1(A_31)
      | v2_relat_1(A_31)
      | ~ v1_funct_1(A_31)
      | ~ v1_relat_1(A_31) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_109,c_204])).

tff(c_218,plain,(
    ! [A_50,B_51] :
      ( ~ r2_hidden('#skF_1'(A_50),k1_relat_1(B_51))
      | ~ v5_funct_1(B_51,A_50)
      | ~ v1_funct_1(B_51)
      | ~ v1_relat_1(B_51)
      | ~ v1_funct_1(A_50)
      | ~ v1_relat_1(A_50)
      | v2_relat_1(A_50)
      | ~ v1_funct_1(A_50)
      | ~ v1_relat_1(A_50) ) ),
    inference(negUnitSimplification,[status(thm)],[c_89,c_210])).

tff(c_224,plain,(
    ! [A_50] :
      ( ~ r2_hidden('#skF_1'(A_50),k1_relat_1('#skF_4'))
      | ~ v5_funct_1('#skF_3',A_50)
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3')
      | ~ v1_funct_1(A_50)
      | ~ v1_relat_1(A_50)
      | v2_relat_1(A_50)
      | ~ v1_funct_1(A_50)
      | ~ v1_relat_1(A_50) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_218])).

tff(c_234,plain,(
    ! [A_53] :
      ( ~ r2_hidden('#skF_1'(A_53),k1_relat_1('#skF_4'))
      | ~ v5_funct_1('#skF_3',A_53)
      | v2_relat_1(A_53)
      | ~ v1_funct_1(A_53)
      | ~ v1_relat_1(A_53) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_224])).

tff(c_238,plain,
    ( ~ v5_funct_1('#skF_3','#skF_4')
    | v2_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_20,c_234])).

tff(c_241,plain,(
    v2_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_36,c_238])).

tff(c_243,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_241])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.11  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n014.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 15:24:37 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.18/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.06/1.22  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.06/1.23  
% 2.06/1.23  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.06/1.23  %$ v5_funct_1 > r2_hidden > v2_relat_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_tarski > k1_funct_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 2.06/1.23  
% 2.06/1.23  %Foreground sorts:
% 2.06/1.23  
% 2.06/1.23  
% 2.06/1.23  %Background operators:
% 2.06/1.23  
% 2.06/1.23  
% 2.06/1.23  %Foreground operators:
% 2.06/1.23  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.06/1.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.06/1.23  tff(v2_relat_1, type, v2_relat_1: $i > $o).
% 2.06/1.23  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.06/1.23  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.06/1.23  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.06/1.23  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.06/1.23  tff(v5_funct_1, type, v5_funct_1: ($i * $i) > $o).
% 2.06/1.23  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.06/1.23  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.06/1.23  tff('#skF_3', type, '#skF_3': $i).
% 2.06/1.23  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.06/1.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.06/1.23  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.06/1.23  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.06/1.23  tff('#skF_4', type, '#skF_4': $i).
% 2.06/1.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.06/1.23  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.06/1.23  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.06/1.23  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.06/1.23  
% 2.06/1.24  tff(f_92, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((v5_funct_1(A, B) & (k1_relat_1(A) = k1_relat_1(B))) => v2_relat_1(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t173_funct_1)).
% 2.06/1.24  tff(f_53, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_relat_1(A) <=> (![B]: ~(r2_hidden(B, k1_relat_1(A)) & v1_xboole_0(k1_funct_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d15_funct_1)).
% 2.06/1.24  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.06/1.24  tff(f_36, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relat_1)).
% 2.06/1.24  tff(f_38, axiom, (![A]: (k10_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t172_relat_1)).
% 2.06/1.24  tff(f_41, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 2.06/1.24  tff(f_76, axiom, (![A, B]: (v1_relat_1(B) => (r2_hidden(A, k2_relat_1(B)) <=> ~(k10_relat_1(B, k1_tarski(A)) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t142_funct_1)).
% 2.06/1.24  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.06/1.24  tff(f_69, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v5_funct_1(B, A) <=> (![C]: (r2_hidden(C, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, C), k1_funct_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d20_funct_1)).
% 2.06/1.24  tff(c_32, plain, (~v2_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.06/1.24  tff(c_40, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.06/1.24  tff(c_38, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.06/1.24  tff(c_36, plain, (v5_funct_1('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.06/1.24  tff(c_20, plain, (![A_5]: (r2_hidden('#skF_1'(A_5), k1_relat_1(A_5)) | v2_relat_1(A_5) | ~v1_funct_1(A_5) | ~v1_relat_1(A_5))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.06/1.24  tff(c_44, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.06/1.24  tff(c_42, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.06/1.24  tff(c_34, plain, (k1_relat_1('#skF_3')=k1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.06/1.24  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.06/1.24  tff(c_57, plain, (![A_22]: (v1_relat_1(A_22) | ~v1_xboole_0(A_22))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.06/1.24  tff(c_61, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_57])).
% 2.06/1.24  tff(c_10, plain, (![A_4]: (k10_relat_1(k1_xboole_0, A_4)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.06/1.24  tff(c_12, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.06/1.24  tff(c_84, plain, (![B_26, A_27]: (k10_relat_1(B_26, k1_tarski(A_27))!=k1_xboole_0 | ~r2_hidden(A_27, k2_relat_1(B_26)) | ~v1_relat_1(B_26))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.06/1.24  tff(c_87, plain, (![A_27]: (k10_relat_1(k1_xboole_0, k1_tarski(A_27))!=k1_xboole_0 | ~r2_hidden(A_27, k1_xboole_0) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_12, c_84])).
% 2.06/1.24  tff(c_89, plain, (![A_27]: (~r2_hidden(A_27, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_61, c_10, c_87])).
% 2.06/1.24  tff(c_102, plain, (![A_31]: (v1_xboole_0(k1_funct_1(A_31, '#skF_1'(A_31))) | v2_relat_1(A_31) | ~v1_funct_1(A_31) | ~v1_relat_1(A_31))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.06/1.24  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 2.06/1.24  tff(c_109, plain, (![A_31]: (k1_funct_1(A_31, '#skF_1'(A_31))=k1_xboole_0 | v2_relat_1(A_31) | ~v1_funct_1(A_31) | ~v1_relat_1(A_31))), inference(resolution, [status(thm)], [c_102, c_4])).
% 2.06/1.24  tff(c_204, plain, (![B_45, C_46, A_47]: (r2_hidden(k1_funct_1(B_45, C_46), k1_funct_1(A_47, C_46)) | ~r2_hidden(C_46, k1_relat_1(B_45)) | ~v5_funct_1(B_45, A_47) | ~v1_funct_1(B_45) | ~v1_relat_1(B_45) | ~v1_funct_1(A_47) | ~v1_relat_1(A_47))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.06/1.24  tff(c_210, plain, (![B_45, A_31]: (r2_hidden(k1_funct_1(B_45, '#skF_1'(A_31)), k1_xboole_0) | ~r2_hidden('#skF_1'(A_31), k1_relat_1(B_45)) | ~v5_funct_1(B_45, A_31) | ~v1_funct_1(B_45) | ~v1_relat_1(B_45) | ~v1_funct_1(A_31) | ~v1_relat_1(A_31) | v2_relat_1(A_31) | ~v1_funct_1(A_31) | ~v1_relat_1(A_31))), inference(superposition, [status(thm), theory('equality')], [c_109, c_204])).
% 2.06/1.24  tff(c_218, plain, (![A_50, B_51]: (~r2_hidden('#skF_1'(A_50), k1_relat_1(B_51)) | ~v5_funct_1(B_51, A_50) | ~v1_funct_1(B_51) | ~v1_relat_1(B_51) | ~v1_funct_1(A_50) | ~v1_relat_1(A_50) | v2_relat_1(A_50) | ~v1_funct_1(A_50) | ~v1_relat_1(A_50))), inference(negUnitSimplification, [status(thm)], [c_89, c_210])).
% 2.06/1.24  tff(c_224, plain, (![A_50]: (~r2_hidden('#skF_1'(A_50), k1_relat_1('#skF_4')) | ~v5_funct_1('#skF_3', A_50) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3') | ~v1_funct_1(A_50) | ~v1_relat_1(A_50) | v2_relat_1(A_50) | ~v1_funct_1(A_50) | ~v1_relat_1(A_50))), inference(superposition, [status(thm), theory('equality')], [c_34, c_218])).
% 2.06/1.24  tff(c_234, plain, (![A_53]: (~r2_hidden('#skF_1'(A_53), k1_relat_1('#skF_4')) | ~v5_funct_1('#skF_3', A_53) | v2_relat_1(A_53) | ~v1_funct_1(A_53) | ~v1_relat_1(A_53))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_224])).
% 2.06/1.24  tff(c_238, plain, (~v5_funct_1('#skF_3', '#skF_4') | v2_relat_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_20, c_234])).
% 2.06/1.24  tff(c_241, plain, (v2_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_36, c_238])).
% 2.06/1.24  tff(c_243, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_241])).
% 2.06/1.24  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.06/1.24  
% 2.06/1.24  Inference rules
% 2.06/1.24  ----------------------
% 2.06/1.24  #Ref     : 0
% 2.06/1.24  #Sup     : 40
% 2.06/1.24  #Fact    : 0
% 2.06/1.24  #Define  : 0
% 2.06/1.24  #Split   : 2
% 2.06/1.24  #Chain   : 0
% 2.06/1.24  #Close   : 0
% 2.06/1.24  
% 2.06/1.24  Ordering : KBO
% 2.06/1.24  
% 2.06/1.24  Simplification rules
% 2.06/1.24  ----------------------
% 2.06/1.24  #Subsume      : 4
% 2.06/1.24  #Demod        : 28
% 2.06/1.24  #Tautology    : 19
% 2.06/1.24  #SimpNegUnit  : 6
% 2.06/1.24  #BackRed      : 0
% 2.06/1.24  
% 2.06/1.24  #Partial instantiations: 0
% 2.06/1.24  #Strategies tried      : 1
% 2.06/1.24  
% 2.06/1.24  Timing (in seconds)
% 2.06/1.24  ----------------------
% 2.06/1.24  Preprocessing        : 0.30
% 2.06/1.24  Parsing              : 0.16
% 2.06/1.24  CNF conversion       : 0.02
% 2.06/1.24  Main loop            : 0.19
% 2.06/1.24  Inferencing          : 0.08
% 2.06/1.24  Reduction            : 0.06
% 2.06/1.24  Demodulation         : 0.04
% 2.06/1.24  BG Simplification    : 0.01
% 2.06/1.24  Subsumption          : 0.03
% 2.06/1.24  Abstraction          : 0.01
% 2.06/1.25  MUC search           : 0.00
% 2.06/1.25  Cooper               : 0.00
% 2.06/1.25  Total                : 0.52
% 2.06/1.25  Index Insertion      : 0.00
% 2.06/1.25  Index Deletion       : 0.00
% 2.06/1.25  Index Matching       : 0.00
% 2.06/1.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------
