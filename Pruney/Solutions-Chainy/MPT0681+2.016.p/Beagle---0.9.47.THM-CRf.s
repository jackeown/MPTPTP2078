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
% DateTime   : Thu Dec  3 10:04:27 EST 2020

% Result     : Theorem 2.77s
% Output     : CNFRefutation 2.77s
% Verified   : 
% Statistics : Number of formulae       :   56 (  63 expanded)
%              Number of leaves         :   29 (  35 expanded)
%              Depth                    :    9
%              Number of atoms          :   74 (  97 expanded)
%              Number of equality atoms :   21 (  24 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff(k6_subset_1,type,(
    k6_subset_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_98,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => ( ( r1_xboole_0(A,B)
            & v2_funct_1(C) )
         => r1_xboole_0(k9_relat_1(C,A),k9_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_funct_1)).

tff(f_63,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_61,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_59,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_57,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_75,axiom,(
    ! [A] :
      ( ~ ( ~ r1_xboole_0(A,A)
          & A = k1_xboole_0 )
      & ~ ( A != k1_xboole_0
          & r1_xboole_0(A,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_xboole_1)).

tff(f_79,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_87,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( v2_funct_1(C)
       => k9_relat_1(C,k6_subset_1(A,B)) = k6_subset_1(k9_relat_1(C,A),k9_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_funct_1)).

tff(f_77,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

tff(c_36,plain,(
    v1_relat_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_34,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_30,plain,(
    v2_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_16,plain,(
    ! [A_14] : k4_xboole_0(A_14,k1_xboole_0) = A_14 ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_14,plain,(
    ! [A_13] : k3_xboole_0(A_13,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_76,plain,(
    ! [A_31,B_32] : k5_xboole_0(A_31,k3_xboole_0(A_31,B_32)) = k4_xboole_0(A_31,B_32) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_85,plain,(
    ! [A_13] : k5_xboole_0(A_13,k1_xboole_0) = k4_xboole_0(A_13,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_76])).

tff(c_88,plain,(
    ! [A_13] : k5_xboole_0(A_13,k1_xboole_0) = A_13 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_85])).

tff(c_32,plain,(
    r1_xboole_0('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_123,plain,(
    ! [A_41,B_42] :
      ( r2_hidden('#skF_1'(A_41,B_42),B_42)
      | r1_xboole_0(A_41,B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_10,plain,(
    ! [A_6,B_7,C_10] :
      ( ~ r1_xboole_0(A_6,B_7)
      | ~ r2_hidden(C_10,k3_xboole_0(A_6,B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_159,plain,(
    ! [A_47,B_48,A_49] :
      ( ~ r1_xboole_0(A_47,B_48)
      | r1_xboole_0(A_49,k3_xboole_0(A_47,B_48)) ) ),
    inference(resolution,[status(thm)],[c_123,c_10])).

tff(c_20,plain,(
    ! [A_15] :
      ( ~ r1_xboole_0(A_15,A_15)
      | k1_xboole_0 = A_15 ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_173,plain,(
    ! [A_50,B_51] :
      ( k3_xboole_0(A_50,B_51) = k1_xboole_0
      | ~ r1_xboole_0(A_50,B_51) ) ),
    inference(resolution,[status(thm)],[c_159,c_20])).

tff(c_194,plain,(
    k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_32,c_173])).

tff(c_12,plain,(
    ! [A_11,B_12] : k5_xboole_0(A_11,k3_xboole_0(A_11,B_12)) = k4_xboole_0(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_233,plain,(
    k5_xboole_0('#skF_3',k1_xboole_0) = k4_xboole_0('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_194,c_12])).

tff(c_240,plain,(
    k4_xboole_0('#skF_3','#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_233])).

tff(c_24,plain,(
    ! [A_18,B_19] : k6_subset_1(A_18,B_19) = k4_xboole_0(A_18,B_19) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_26,plain,(
    ! [C_22,A_20,B_21] :
      ( k6_subset_1(k9_relat_1(C_22,A_20),k9_relat_1(C_22,B_21)) = k9_relat_1(C_22,k6_subset_1(A_20,B_21))
      | ~ v2_funct_1(C_22)
      | ~ v1_funct_1(C_22)
      | ~ v1_relat_1(C_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_446,plain,(
    ! [C_65,A_66,B_67] :
      ( k4_xboole_0(k9_relat_1(C_65,A_66),k9_relat_1(C_65,B_67)) = k9_relat_1(C_65,k4_xboole_0(A_66,B_67))
      | ~ v2_funct_1(C_65)
      | ~ v1_funct_1(C_65)
      | ~ v1_relat_1(C_65) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_24,c_26])).

tff(c_22,plain,(
    ! [A_16,B_17] : r1_xboole_0(k4_xboole_0(A_16,B_17),B_17) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_918,plain,(
    ! [C_90,A_91,B_92] :
      ( r1_xboole_0(k9_relat_1(C_90,k4_xboole_0(A_91,B_92)),k9_relat_1(C_90,B_92))
      | ~ v2_funct_1(C_90)
      | ~ v1_funct_1(C_90)
      | ~ v1_relat_1(C_90) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_446,c_22])).

tff(c_1183,plain,(
    ! [C_99] :
      ( r1_xboole_0(k9_relat_1(C_99,'#skF_3'),k9_relat_1(C_99,'#skF_4'))
      | ~ v2_funct_1(C_99)
      | ~ v1_funct_1(C_99)
      | ~ v1_relat_1(C_99) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_240,c_918])).

tff(c_28,plain,(
    ~ r1_xboole_0(k9_relat_1('#skF_5','#skF_3'),k9_relat_1('#skF_5','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_1191,plain,
    ( ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_1183,c_28])).

tff(c_1197,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_30,c_1191])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:47:59 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.77/1.40  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.77/1.41  
% 2.77/1.41  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.77/1.41  %$ r2_hidden > r1_xboole_0 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.77/1.41  
% 2.77/1.41  %Foreground sorts:
% 2.77/1.41  
% 2.77/1.41  
% 2.77/1.41  %Background operators:
% 2.77/1.41  
% 2.77/1.41  
% 2.77/1.41  %Foreground operators:
% 2.77/1.41  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.77/1.41  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 2.77/1.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.77/1.41  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.77/1.41  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.77/1.41  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.77/1.41  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.77/1.41  tff('#skF_5', type, '#skF_5': $i).
% 2.77/1.41  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.77/1.41  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.77/1.41  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 2.77/1.41  tff('#skF_3', type, '#skF_3': $i).
% 2.77/1.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.77/1.41  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.77/1.41  tff('#skF_4', type, '#skF_4': $i).
% 2.77/1.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.77/1.41  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.77/1.41  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.77/1.41  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.77/1.41  
% 2.77/1.42  tff(f_98, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((r1_xboole_0(A, B) & v2_funct_1(C)) => r1_xboole_0(k9_relat_1(C, A), k9_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t125_funct_1)).
% 2.77/1.42  tff(f_63, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 2.77/1.42  tff(f_61, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 2.77/1.42  tff(f_59, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.77/1.42  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 2.77/1.42  tff(f_57, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.77/1.42  tff(f_75, axiom, (![A]: (~(~r1_xboole_0(A, A) & (A = k1_xboole_0)) & ~(~(A = k1_xboole_0) & r1_xboole_0(A, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t66_xboole_1)).
% 2.77/1.42  tff(f_79, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 2.77/1.42  tff(f_87, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (v2_funct_1(C) => (k9_relat_1(C, k6_subset_1(A, B)) = k6_subset_1(k9_relat_1(C, A), k9_relat_1(C, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t123_funct_1)).
% 2.77/1.42  tff(f_77, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 2.77/1.42  tff(c_36, plain, (v1_relat_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.77/1.42  tff(c_34, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.77/1.42  tff(c_30, plain, (v2_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.77/1.42  tff(c_16, plain, (![A_14]: (k4_xboole_0(A_14, k1_xboole_0)=A_14)), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.77/1.42  tff(c_14, plain, (![A_13]: (k3_xboole_0(A_13, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.77/1.42  tff(c_76, plain, (![A_31, B_32]: (k5_xboole_0(A_31, k3_xboole_0(A_31, B_32))=k4_xboole_0(A_31, B_32))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.77/1.42  tff(c_85, plain, (![A_13]: (k5_xboole_0(A_13, k1_xboole_0)=k4_xboole_0(A_13, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_14, c_76])).
% 2.77/1.42  tff(c_88, plain, (![A_13]: (k5_xboole_0(A_13, k1_xboole_0)=A_13)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_85])).
% 2.77/1.42  tff(c_32, plain, (r1_xboole_0('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.77/1.42  tff(c_123, plain, (![A_41, B_42]: (r2_hidden('#skF_1'(A_41, B_42), B_42) | r1_xboole_0(A_41, B_42))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.77/1.42  tff(c_10, plain, (![A_6, B_7, C_10]: (~r1_xboole_0(A_6, B_7) | ~r2_hidden(C_10, k3_xboole_0(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.77/1.42  tff(c_159, plain, (![A_47, B_48, A_49]: (~r1_xboole_0(A_47, B_48) | r1_xboole_0(A_49, k3_xboole_0(A_47, B_48)))), inference(resolution, [status(thm)], [c_123, c_10])).
% 2.77/1.42  tff(c_20, plain, (![A_15]: (~r1_xboole_0(A_15, A_15) | k1_xboole_0=A_15)), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.77/1.42  tff(c_173, plain, (![A_50, B_51]: (k3_xboole_0(A_50, B_51)=k1_xboole_0 | ~r1_xboole_0(A_50, B_51))), inference(resolution, [status(thm)], [c_159, c_20])).
% 2.77/1.42  tff(c_194, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_32, c_173])).
% 2.77/1.42  tff(c_12, plain, (![A_11, B_12]: (k5_xboole_0(A_11, k3_xboole_0(A_11, B_12))=k4_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.77/1.42  tff(c_233, plain, (k5_xboole_0('#skF_3', k1_xboole_0)=k4_xboole_0('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_194, c_12])).
% 2.77/1.42  tff(c_240, plain, (k4_xboole_0('#skF_3', '#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_88, c_233])).
% 2.77/1.42  tff(c_24, plain, (![A_18, B_19]: (k6_subset_1(A_18, B_19)=k4_xboole_0(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.77/1.42  tff(c_26, plain, (![C_22, A_20, B_21]: (k6_subset_1(k9_relat_1(C_22, A_20), k9_relat_1(C_22, B_21))=k9_relat_1(C_22, k6_subset_1(A_20, B_21)) | ~v2_funct_1(C_22) | ~v1_funct_1(C_22) | ~v1_relat_1(C_22))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.77/1.42  tff(c_446, plain, (![C_65, A_66, B_67]: (k4_xboole_0(k9_relat_1(C_65, A_66), k9_relat_1(C_65, B_67))=k9_relat_1(C_65, k4_xboole_0(A_66, B_67)) | ~v2_funct_1(C_65) | ~v1_funct_1(C_65) | ~v1_relat_1(C_65))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_24, c_26])).
% 2.77/1.42  tff(c_22, plain, (![A_16, B_17]: (r1_xboole_0(k4_xboole_0(A_16, B_17), B_17))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.77/1.42  tff(c_918, plain, (![C_90, A_91, B_92]: (r1_xboole_0(k9_relat_1(C_90, k4_xboole_0(A_91, B_92)), k9_relat_1(C_90, B_92)) | ~v2_funct_1(C_90) | ~v1_funct_1(C_90) | ~v1_relat_1(C_90))), inference(superposition, [status(thm), theory('equality')], [c_446, c_22])).
% 2.77/1.42  tff(c_1183, plain, (![C_99]: (r1_xboole_0(k9_relat_1(C_99, '#skF_3'), k9_relat_1(C_99, '#skF_4')) | ~v2_funct_1(C_99) | ~v1_funct_1(C_99) | ~v1_relat_1(C_99))), inference(superposition, [status(thm), theory('equality')], [c_240, c_918])).
% 2.77/1.42  tff(c_28, plain, (~r1_xboole_0(k9_relat_1('#skF_5', '#skF_3'), k9_relat_1('#skF_5', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.77/1.42  tff(c_1191, plain, (~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_1183, c_28])).
% 2.77/1.42  tff(c_1197, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_30, c_1191])).
% 2.77/1.42  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.77/1.42  
% 2.77/1.42  Inference rules
% 2.77/1.42  ----------------------
% 2.77/1.42  #Ref     : 0
% 2.77/1.42  #Sup     : 277
% 2.77/1.42  #Fact    : 0
% 2.77/1.42  #Define  : 0
% 2.77/1.42  #Split   : 0
% 2.77/1.42  #Chain   : 0
% 2.77/1.42  #Close   : 0
% 2.77/1.42  
% 2.77/1.42  Ordering : KBO
% 2.77/1.42  
% 2.77/1.42  Simplification rules
% 2.77/1.42  ----------------------
% 2.77/1.42  #Subsume      : 43
% 2.77/1.42  #Demod        : 185
% 2.77/1.42  #Tautology    : 176
% 2.77/1.42  #SimpNegUnit  : 8
% 2.77/1.42  #BackRed      : 0
% 2.77/1.42  
% 2.77/1.42  #Partial instantiations: 0
% 2.77/1.42  #Strategies tried      : 1
% 2.77/1.42  
% 2.77/1.42  Timing (in seconds)
% 2.77/1.42  ----------------------
% 2.77/1.43  Preprocessing        : 0.30
% 2.77/1.43  Parsing              : 0.16
% 2.77/1.43  CNF conversion       : 0.02
% 2.77/1.43  Main loop            : 0.34
% 2.77/1.43  Inferencing          : 0.13
% 2.77/1.43  Reduction            : 0.12
% 2.77/1.43  Demodulation         : 0.09
% 2.77/1.43  BG Simplification    : 0.02
% 2.77/1.43  Subsumption          : 0.06
% 2.77/1.43  Abstraction          : 0.02
% 2.77/1.43  MUC search           : 0.00
% 2.77/1.43  Cooper               : 0.00
% 2.77/1.43  Total                : 0.67
% 2.77/1.43  Index Insertion      : 0.00
% 2.77/1.43  Index Deletion       : 0.00
% 2.77/1.43  Index Matching       : 0.00
% 2.77/1.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
