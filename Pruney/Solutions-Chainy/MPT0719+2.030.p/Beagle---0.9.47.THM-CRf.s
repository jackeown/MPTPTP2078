%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:47 EST 2020

% Result     : Theorem 2.19s
% Output     : CNFRefutation 2.33s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 117 expanded)
%              Number of leaves         :   33 (  55 expanded)
%              Depth                    :   11
%              Number of atoms          :   90 ( 191 expanded)
%              Number of equality atoms :    7 (  21 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_funct_1 > r2_hidden > r1_xboole_0 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_tarski > k2_tarski > k1_funct_1 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_3 > #skF_6 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(v5_funct_1,type,(
    v5_funct_1: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_91,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => v5_funct_1(k1_xboole_0,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t174_funct_1)).

tff(f_37,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ~ ( r1_xboole_0(k2_tarski(A,B),C)
        & r2_hidden(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_zfmisc_1)).

tff(f_64,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_xboole_0(k1_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc10_relat_1)).

tff(f_35,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_60,axiom,(
    ! [A] :
      ( v1_relat_1(A)
    <=> ! [B] :
          ~ ( r2_hidden(B,A)
            & ! [C,D] : B != k4_tarski(C,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_relat_1)).

tff(f_68,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_funct_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_funct_1)).

tff(f_84,axiom,(
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

tff(c_40,plain,(
    v1_relat_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_38,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_8,plain,(
    ! [A_6] : r1_xboole_0(A_6,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_158,plain,(
    ! [A_79,C_80,B_81] :
      ( ~ r2_hidden(A_79,C_80)
      | ~ r1_xboole_0(k2_tarski(A_79,B_81),C_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_163,plain,(
    ! [A_79] : ~ r2_hidden(A_79,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_8,c_158])).

tff(c_26,plain,(
    ! [A_42] :
      ( v1_xboole_0(k1_relat_1(A_42))
      | ~ v1_xboole_0(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_45,plain,(
    ! [A_59] :
      ( v1_xboole_0(k1_relat_1(A_59))
      | ~ v1_xboole_0(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_6,plain,(
    ! [A_5] :
      ( k1_xboole_0 = A_5
      | ~ v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_65,plain,(
    ! [A_63] :
      ( k1_relat_1(A_63) = k1_xboole_0
      | ~ v1_xboole_0(A_63) ) ),
    inference(resolution,[status(thm)],[c_45,c_6])).

tff(c_76,plain,(
    ! [A_66] :
      ( k1_relat_1(k1_relat_1(A_66)) = k1_xboole_0
      | ~ v1_xboole_0(A_66) ) ),
    inference(resolution,[status(thm)],[c_26,c_65])).

tff(c_91,plain,(
    ! [A_66] :
      ( v1_xboole_0(k1_xboole_0)
      | ~ v1_xboole_0(k1_relat_1(A_66))
      | ~ v1_xboole_0(A_66) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_76,c_26])).

tff(c_111,plain,(
    ! [A_72] :
      ( ~ v1_xboole_0(k1_relat_1(A_72))
      | ~ v1_xboole_0(A_72) ) ),
    inference(splitLeft,[status(thm)],[c_91])).

tff(c_118,plain,(
    ! [A_42] : ~ v1_xboole_0(A_42) ),
    inference(resolution,[status(thm)],[c_26,c_111])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_134,plain,(
    ! [A_78] : r2_hidden('#skF_1'(A_78),A_78) ),
    inference(negUnitSimplification,[status(thm)],[c_118,c_4])).

tff(c_119,plain,(
    ! [A_73,C_74,B_75] :
      ( ~ r2_hidden(A_73,C_74)
      | ~ r1_xboole_0(k2_tarski(A_73,B_75),C_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_124,plain,(
    ! [A_73] : ~ r2_hidden(A_73,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_8,c_119])).

tff(c_139,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_134,c_124])).

tff(c_140,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_91])).

tff(c_55,plain,(
    ! [A_61] :
      ( r2_hidden('#skF_2'(A_61),A_61)
      | v1_relat_1(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_59,plain,(
    ! [A_61] :
      ( ~ v1_xboole_0(A_61)
      | v1_relat_1(A_61) ) ),
    inference(resolution,[status(thm)],[c_55,c_2])).

tff(c_154,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_140,c_59])).

tff(c_28,plain,(
    ! [A_43] :
      ( v1_funct_1(A_43)
      | ~ v1_xboole_0(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_155,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_140,c_28])).

tff(c_53,plain,(
    ! [A_59] :
      ( k1_relat_1(A_59) = k1_xboole_0
      | ~ v1_xboole_0(A_59) ) ),
    inference(resolution,[status(thm)],[c_45,c_6])).

tff(c_153,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_140,c_53])).

tff(c_247,plain,(
    ! [A_100,B_101] :
      ( r2_hidden('#skF_5'(A_100,B_101),k1_relat_1(B_101))
      | v5_funct_1(B_101,A_100)
      | ~ v1_funct_1(B_101)
      | ~ v1_relat_1(B_101)
      | ~ v1_funct_1(A_100)
      | ~ v1_relat_1(A_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_253,plain,(
    ! [A_100] :
      ( r2_hidden('#skF_5'(A_100,k1_xboole_0),k1_xboole_0)
      | v5_funct_1(k1_xboole_0,A_100)
      | ~ v1_funct_1(k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_funct_1(A_100)
      | ~ v1_relat_1(A_100) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_153,c_247])).

tff(c_259,plain,(
    ! [A_100] :
      ( r2_hidden('#skF_5'(A_100,k1_xboole_0),k1_xboole_0)
      | v5_funct_1(k1_xboole_0,A_100)
      | ~ v1_funct_1(A_100)
      | ~ v1_relat_1(A_100) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_155,c_253])).

tff(c_262,plain,(
    ! [A_102] :
      ( v5_funct_1(k1_xboole_0,A_102)
      | ~ v1_funct_1(A_102)
      | ~ v1_relat_1(A_102) ) ),
    inference(negUnitSimplification,[status(thm)],[c_163,c_259])).

tff(c_36,plain,(
    ~ v5_funct_1(k1_xboole_0,'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_265,plain,
    ( ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_262,c_36])).

tff(c_269,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_265])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:34:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.19/1.23  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.32/1.23  
% 2.32/1.23  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.33/1.24  %$ v5_funct_1 > r2_hidden > r1_xboole_0 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_tarski > k2_tarski > k1_funct_1 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_3 > #skF_6 > #skF_5 > #skF_4
% 2.33/1.24  
% 2.33/1.24  %Foreground sorts:
% 2.33/1.24  
% 2.33/1.24  
% 2.33/1.24  %Background operators:
% 2.33/1.24  
% 2.33/1.24  
% 2.33/1.24  %Foreground operators:
% 2.33/1.24  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.33/1.24  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.33/1.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.33/1.24  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.33/1.24  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.33/1.24  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.33/1.24  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.33/1.24  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.33/1.24  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.33/1.24  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.33/1.24  tff(v5_funct_1, type, v5_funct_1: ($i * $i) > $o).
% 2.33/1.24  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.33/1.24  tff('#skF_6', type, '#skF_6': $i).
% 2.33/1.24  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.33/1.24  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.33/1.24  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.33/1.24  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.33/1.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.33/1.24  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.33/1.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.33/1.24  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.33/1.24  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 2.33/1.24  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.33/1.24  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.33/1.24  
% 2.33/1.25  tff(f_91, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => v5_funct_1(k1_xboole_0, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t174_funct_1)).
% 2.33/1.25  tff(f_37, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.33/1.25  tff(f_50, axiom, (![A, B, C]: ~(r1_xboole_0(k2_tarski(A, B), C) & r2_hidden(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_zfmisc_1)).
% 2.33/1.25  tff(f_64, axiom, (![A]: (v1_xboole_0(A) => v1_xboole_0(k1_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc10_relat_1)).
% 2.33/1.25  tff(f_35, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.33/1.25  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.33/1.25  tff(f_60, axiom, (![A]: (v1_relat_1(A) <=> (![B]: ~(r2_hidden(B, A) & (![C, D]: ~(B = k4_tarski(C, D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_relat_1)).
% 2.33/1.25  tff(f_68, axiom, (![A]: (v1_xboole_0(A) => v1_funct_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_funct_1)).
% 2.33/1.25  tff(f_84, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v5_funct_1(B, A) <=> (![C]: (r2_hidden(C, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, C), k1_funct_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d20_funct_1)).
% 2.33/1.25  tff(c_40, plain, (v1_relat_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.33/1.25  tff(c_38, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.33/1.25  tff(c_8, plain, (![A_6]: (r1_xboole_0(A_6, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.33/1.25  tff(c_158, plain, (![A_79, C_80, B_81]: (~r2_hidden(A_79, C_80) | ~r1_xboole_0(k2_tarski(A_79, B_81), C_80))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.33/1.25  tff(c_163, plain, (![A_79]: (~r2_hidden(A_79, k1_xboole_0))), inference(resolution, [status(thm)], [c_8, c_158])).
% 2.33/1.25  tff(c_26, plain, (![A_42]: (v1_xboole_0(k1_relat_1(A_42)) | ~v1_xboole_0(A_42))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.33/1.25  tff(c_45, plain, (![A_59]: (v1_xboole_0(k1_relat_1(A_59)) | ~v1_xboole_0(A_59))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.33/1.25  tff(c_6, plain, (![A_5]: (k1_xboole_0=A_5 | ~v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.33/1.25  tff(c_65, plain, (![A_63]: (k1_relat_1(A_63)=k1_xboole_0 | ~v1_xboole_0(A_63))), inference(resolution, [status(thm)], [c_45, c_6])).
% 2.33/1.25  tff(c_76, plain, (![A_66]: (k1_relat_1(k1_relat_1(A_66))=k1_xboole_0 | ~v1_xboole_0(A_66))), inference(resolution, [status(thm)], [c_26, c_65])).
% 2.33/1.25  tff(c_91, plain, (![A_66]: (v1_xboole_0(k1_xboole_0) | ~v1_xboole_0(k1_relat_1(A_66)) | ~v1_xboole_0(A_66))), inference(superposition, [status(thm), theory('equality')], [c_76, c_26])).
% 2.33/1.25  tff(c_111, plain, (![A_72]: (~v1_xboole_0(k1_relat_1(A_72)) | ~v1_xboole_0(A_72))), inference(splitLeft, [status(thm)], [c_91])).
% 2.33/1.25  tff(c_118, plain, (![A_42]: (~v1_xboole_0(A_42))), inference(resolution, [status(thm)], [c_26, c_111])).
% 2.33/1.25  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.33/1.25  tff(c_134, plain, (![A_78]: (r2_hidden('#skF_1'(A_78), A_78))), inference(negUnitSimplification, [status(thm)], [c_118, c_4])).
% 2.33/1.25  tff(c_119, plain, (![A_73, C_74, B_75]: (~r2_hidden(A_73, C_74) | ~r1_xboole_0(k2_tarski(A_73, B_75), C_74))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.33/1.25  tff(c_124, plain, (![A_73]: (~r2_hidden(A_73, k1_xboole_0))), inference(resolution, [status(thm)], [c_8, c_119])).
% 2.33/1.25  tff(c_139, plain, $false, inference(resolution, [status(thm)], [c_134, c_124])).
% 2.33/1.25  tff(c_140, plain, (v1_xboole_0(k1_xboole_0)), inference(splitRight, [status(thm)], [c_91])).
% 2.33/1.25  tff(c_55, plain, (![A_61]: (r2_hidden('#skF_2'(A_61), A_61) | v1_relat_1(A_61))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.33/1.25  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.33/1.25  tff(c_59, plain, (![A_61]: (~v1_xboole_0(A_61) | v1_relat_1(A_61))), inference(resolution, [status(thm)], [c_55, c_2])).
% 2.33/1.25  tff(c_154, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_140, c_59])).
% 2.33/1.25  tff(c_28, plain, (![A_43]: (v1_funct_1(A_43) | ~v1_xboole_0(A_43))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.33/1.25  tff(c_155, plain, (v1_funct_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_140, c_28])).
% 2.33/1.25  tff(c_53, plain, (![A_59]: (k1_relat_1(A_59)=k1_xboole_0 | ~v1_xboole_0(A_59))), inference(resolution, [status(thm)], [c_45, c_6])).
% 2.33/1.25  tff(c_153, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_140, c_53])).
% 2.33/1.25  tff(c_247, plain, (![A_100, B_101]: (r2_hidden('#skF_5'(A_100, B_101), k1_relat_1(B_101)) | v5_funct_1(B_101, A_100) | ~v1_funct_1(B_101) | ~v1_relat_1(B_101) | ~v1_funct_1(A_100) | ~v1_relat_1(A_100))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.33/1.25  tff(c_253, plain, (![A_100]: (r2_hidden('#skF_5'(A_100, k1_xboole_0), k1_xboole_0) | v5_funct_1(k1_xboole_0, A_100) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~v1_funct_1(A_100) | ~v1_relat_1(A_100))), inference(superposition, [status(thm), theory('equality')], [c_153, c_247])).
% 2.33/1.25  tff(c_259, plain, (![A_100]: (r2_hidden('#skF_5'(A_100, k1_xboole_0), k1_xboole_0) | v5_funct_1(k1_xboole_0, A_100) | ~v1_funct_1(A_100) | ~v1_relat_1(A_100))), inference(demodulation, [status(thm), theory('equality')], [c_154, c_155, c_253])).
% 2.33/1.25  tff(c_262, plain, (![A_102]: (v5_funct_1(k1_xboole_0, A_102) | ~v1_funct_1(A_102) | ~v1_relat_1(A_102))), inference(negUnitSimplification, [status(thm)], [c_163, c_259])).
% 2.33/1.25  tff(c_36, plain, (~v5_funct_1(k1_xboole_0, '#skF_6')), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.33/1.25  tff(c_265, plain, (~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_262, c_36])).
% 2.33/1.25  tff(c_269, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_265])).
% 2.33/1.25  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.33/1.25  
% 2.33/1.25  Inference rules
% 2.33/1.25  ----------------------
% 2.33/1.25  #Ref     : 1
% 2.33/1.25  #Sup     : 46
% 2.33/1.25  #Fact    : 0
% 2.33/1.25  #Define  : 0
% 2.33/1.25  #Split   : 1
% 2.33/1.25  #Chain   : 0
% 2.33/1.25  #Close   : 0
% 2.33/1.25  
% 2.33/1.25  Ordering : KBO
% 2.33/1.25  
% 2.33/1.25  Simplification rules
% 2.33/1.25  ----------------------
% 2.33/1.25  #Subsume      : 11
% 2.33/1.25  #Demod        : 18
% 2.33/1.25  #Tautology    : 26
% 2.33/1.25  #SimpNegUnit  : 4
% 2.33/1.25  #BackRed      : 1
% 2.33/1.25  
% 2.33/1.25  #Partial instantiations: 0
% 2.33/1.25  #Strategies tried      : 1
% 2.33/1.25  
% 2.33/1.25  Timing (in seconds)
% 2.33/1.25  ----------------------
% 2.33/1.25  Preprocessing        : 0.31
% 2.33/1.25  Parsing              : 0.16
% 2.33/1.25  CNF conversion       : 0.02
% 2.33/1.25  Main loop            : 0.18
% 2.33/1.25  Inferencing          : 0.08
% 2.33/1.25  Reduction            : 0.05
% 2.33/1.25  Demodulation         : 0.03
% 2.33/1.25  BG Simplification    : 0.02
% 2.33/1.25  Subsumption          : 0.03
% 2.33/1.25  Abstraction          : 0.01
% 2.33/1.25  MUC search           : 0.00
% 2.33/1.25  Cooper               : 0.00
% 2.33/1.26  Total                : 0.52
% 2.33/1.26  Index Insertion      : 0.00
% 2.33/1.26  Index Deletion       : 0.00
% 2.33/1.26  Index Matching       : 0.00
% 2.33/1.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------
