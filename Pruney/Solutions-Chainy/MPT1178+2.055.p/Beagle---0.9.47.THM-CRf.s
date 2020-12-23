%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:09 EST 2020

% Result     : Theorem 1.99s
% Output     : CNFRefutation 2.21s
% Verified   : 
% Statistics : Number of formulae       :   57 ( 104 expanded)
%              Number of leaves         :   30 (  55 expanded)
%              Depth                    :   11
%              Number of atoms          :  123 ( 332 expanded)
%              Number of equality atoms :    3 (  27 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m2_orders_2 > r2_hidden > r1_tarski > m1_orders_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_orders_2 > k4_orders_2 > k1_funct_1 > #nlpp > u1_struct_0 > k3_tarski > k1_orders_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k4_orders_2,type,(
    k4_orders_2: ( $i * $i ) > $i )).

tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v3_orders_2,type,(
    v3_orders_2: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(m1_orders_1,type,(
    m1_orders_1: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(m2_orders_2,type,(
    m2_orders_2: ( $i * $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(v4_orders_2,type,(
    v4_orders_2: $i > $o )).

tff(v5_orders_2,type,(
    v5_orders_2: $i > $o )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff(k1_orders_1,type,(
    k1_orders_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(f_113,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v3_orders_2(A)
          & v4_orders_2(A)
          & v5_orders_2(A)
          & l1_orders_2(A) )
       => ! [B] :
            ( m1_orders_1(B,k1_orders_1(u1_struct_0(A)))
           => k3_tarski(k4_orders_2(A,B)) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_orders_2)).

tff(f_76,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A)
        & m1_orders_1(B,k1_orders_1(u1_struct_0(A))) )
     => ? [C] : m2_orders_2(C,A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m2_orders_2)).

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_60,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_orders_1(B,k1_orders_1(u1_struct_0(A)))
         => ! [C] :
              ( C = k4_orders_2(A,B)
            <=> ! [D] :
                  ( r2_hidden(D,C)
                <=> m2_orders_2(D,A,B) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d17_orders_2)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(k3_tarski(A),B)
        & r2_hidden(C,A) )
     => r1_tarski(C,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_setfam_1)).

tff(f_95,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_orders_1(B,k1_orders_1(u1_struct_0(A)))
         => ! [C] :
              ( m2_orders_2(C,A,B)
             => r2_hidden(k1_funct_1(B,u1_struct_0(A)),C) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_orders_2)).

tff(f_38,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_36,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_34,plain,(
    v3_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_32,plain,(
    v4_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_30,plain,(
    v5_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_28,plain,(
    l1_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_26,plain,(
    m1_orders_1('#skF_5',k1_orders_1(u1_struct_0('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_44,plain,(
    ! [A_46,B_47] :
      ( m2_orders_2('#skF_3'(A_46,B_47),A_46,B_47)
      | ~ m1_orders_1(B_47,k1_orders_1(u1_struct_0(A_46)))
      | ~ l1_orders_2(A_46)
      | ~ v5_orders_2(A_46)
      | ~ v4_orders_2(A_46)
      | ~ v3_orders_2(A_46)
      | v2_struct_0(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_46,plain,
    ( m2_orders_2('#skF_3'('#skF_4','#skF_5'),'#skF_4','#skF_5')
    | ~ l1_orders_2('#skF_4')
    | ~ v5_orders_2('#skF_4')
    | ~ v4_orders_2('#skF_4')
    | ~ v3_orders_2('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_26,c_44])).

tff(c_49,plain,
    ( m2_orders_2('#skF_3'('#skF_4','#skF_5'),'#skF_4','#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_30,c_28,c_46])).

tff(c_50,plain,(
    m2_orders_2('#skF_3'('#skF_4','#skF_5'),'#skF_4','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_49])).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_24,plain,(
    k3_tarski(k4_orders_2('#skF_4','#skF_5')) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_51,plain,(
    ! [D_48,A_49,B_50] :
      ( r2_hidden(D_48,k4_orders_2(A_49,B_50))
      | ~ m2_orders_2(D_48,A_49,B_50)
      | ~ m1_orders_1(B_50,k1_orders_1(u1_struct_0(A_49)))
      | ~ l1_orders_2(A_49)
      | ~ v5_orders_2(A_49)
      | ~ v4_orders_2(A_49)
      | ~ v3_orders_2(A_49)
      | v2_struct_0(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_53,plain,(
    ! [D_48] :
      ( r2_hidden(D_48,k4_orders_2('#skF_4','#skF_5'))
      | ~ m2_orders_2(D_48,'#skF_4','#skF_5')
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4')
      | ~ v4_orders_2('#skF_4')
      | ~ v3_orders_2('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_26,c_51])).

tff(c_56,plain,(
    ! [D_48] :
      ( r2_hidden(D_48,k4_orders_2('#skF_4','#skF_5'))
      | ~ m2_orders_2(D_48,'#skF_4','#skF_5')
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_30,c_28,c_53])).

tff(c_58,plain,(
    ! [D_51] :
      ( r2_hidden(D_51,k4_orders_2('#skF_4','#skF_5'))
      | ~ m2_orders_2(D_51,'#skF_4','#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_56])).

tff(c_4,plain,(
    ! [C_4,B_3,A_2] :
      ( r1_tarski(C_4,B_3)
      | ~ r2_hidden(C_4,A_2)
      | ~ r1_tarski(k3_tarski(A_2),B_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_60,plain,(
    ! [D_51,B_3] :
      ( r1_tarski(D_51,B_3)
      | ~ r1_tarski(k3_tarski(k4_orders_2('#skF_4','#skF_5')),B_3)
      | ~ m2_orders_2(D_51,'#skF_4','#skF_5') ) ),
    inference(resolution,[status(thm)],[c_58,c_4])).

tff(c_68,plain,(
    ! [D_52,B_53] :
      ( r1_tarski(D_52,B_53)
      | ~ m2_orders_2(D_52,'#skF_4','#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_24,c_60])).

tff(c_71,plain,(
    ! [B_53] : r1_tarski('#skF_3'('#skF_4','#skF_5'),B_53) ),
    inference(resolution,[status(thm)],[c_50,c_68])).

tff(c_81,plain,(
    ! [B_59,A_60,C_61] :
      ( r2_hidden(k1_funct_1(B_59,u1_struct_0(A_60)),C_61)
      | ~ m2_orders_2(C_61,A_60,B_59)
      | ~ m1_orders_1(B_59,k1_orders_1(u1_struct_0(A_60)))
      | ~ l1_orders_2(A_60)
      | ~ v5_orders_2(A_60)
      | ~ v4_orders_2(A_60)
      | ~ v3_orders_2(A_60)
      | v2_struct_0(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_6,plain,(
    ! [B_6,A_5] :
      ( ~ r1_tarski(B_6,A_5)
      | ~ r2_hidden(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_98,plain,(
    ! [C_65,B_66,A_67] :
      ( ~ r1_tarski(C_65,k1_funct_1(B_66,u1_struct_0(A_67)))
      | ~ m2_orders_2(C_65,A_67,B_66)
      | ~ m1_orders_1(B_66,k1_orders_1(u1_struct_0(A_67)))
      | ~ l1_orders_2(A_67)
      | ~ v5_orders_2(A_67)
      | ~ v4_orders_2(A_67)
      | ~ v3_orders_2(A_67)
      | v2_struct_0(A_67) ) ),
    inference(resolution,[status(thm)],[c_81,c_6])).

tff(c_117,plain,(
    ! [A_70,B_71] :
      ( ~ m2_orders_2('#skF_3'('#skF_4','#skF_5'),A_70,B_71)
      | ~ m1_orders_1(B_71,k1_orders_1(u1_struct_0(A_70)))
      | ~ l1_orders_2(A_70)
      | ~ v5_orders_2(A_70)
      | ~ v4_orders_2(A_70)
      | ~ v3_orders_2(A_70)
      | v2_struct_0(A_70) ) ),
    inference(resolution,[status(thm)],[c_71,c_98])).

tff(c_120,plain,
    ( ~ m2_orders_2('#skF_3'('#skF_4','#skF_5'),'#skF_4','#skF_5')
    | ~ l1_orders_2('#skF_4')
    | ~ v5_orders_2('#skF_4')
    | ~ v4_orders_2('#skF_4')
    | ~ v3_orders_2('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_26,c_117])).

tff(c_123,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_30,c_28,c_50,c_120])).

tff(c_125,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_123])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 14:54:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.99/1.30  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.99/1.30  
% 1.99/1.30  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.99/1.30  %$ m2_orders_2 > r2_hidden > r1_tarski > m1_orders_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_orders_2 > k4_orders_2 > k1_funct_1 > #nlpp > u1_struct_0 > k3_tarski > k1_orders_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_2 > #skF_4
% 1.99/1.30  
% 1.99/1.30  %Foreground sorts:
% 1.99/1.30  
% 1.99/1.30  
% 1.99/1.30  %Background operators:
% 1.99/1.30  
% 1.99/1.30  
% 1.99/1.30  %Foreground operators:
% 1.99/1.30  tff(k4_orders_2, type, k4_orders_2: ($i * $i) > $i).
% 1.99/1.30  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 1.99/1.30  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 1.99/1.30  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 1.99/1.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.99/1.30  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.99/1.30  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.99/1.30  tff(m1_orders_1, type, m1_orders_1: ($i * $i) > $o).
% 1.99/1.30  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 1.99/1.30  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.99/1.30  tff(m2_orders_2, type, m2_orders_2: ($i * $i * $i) > $o).
% 1.99/1.30  tff('#skF_5', type, '#skF_5': $i).
% 1.99/1.30  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.99/1.30  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 1.99/1.30  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 1.99/1.30  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 1.99/1.30  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 1.99/1.30  tff(k1_orders_1, type, k1_orders_1: $i > $i).
% 1.99/1.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.99/1.30  tff(k3_tarski, type, k3_tarski: $i > $i).
% 1.99/1.30  tff('#skF_4', type, '#skF_4': $i).
% 1.99/1.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.99/1.30  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 1.99/1.30  
% 2.21/1.32  tff(f_113, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => ~(k3_tarski(k4_orders_2(A, B)) = k1_xboole_0))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_orders_2)).
% 2.21/1.32  tff(f_76, axiom, (![A, B]: ((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) & m1_orders_1(B, k1_orders_1(u1_struct_0(A)))) => (?[C]: m2_orders_2(C, A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', existence_m2_orders_2)).
% 2.21/1.32  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.21/1.32  tff(f_60, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: ((C = k4_orders_2(A, B)) <=> (![D]: (r2_hidden(D, C) <=> m2_orders_2(D, A, B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d17_orders_2)).
% 2.21/1.32  tff(f_33, axiom, (![A, B, C]: ((r1_tarski(k3_tarski(A), B) & r2_hidden(C, A)) => r1_tarski(C, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t56_setfam_1)).
% 2.21/1.32  tff(f_95, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: (m2_orders_2(C, A, B) => r2_hidden(k1_funct_1(B, u1_struct_0(A)), C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_orders_2)).
% 2.21/1.32  tff(f_38, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 2.21/1.32  tff(c_36, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.21/1.32  tff(c_34, plain, (v3_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.21/1.32  tff(c_32, plain, (v4_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.21/1.32  tff(c_30, plain, (v5_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.21/1.32  tff(c_28, plain, (l1_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.21/1.32  tff(c_26, plain, (m1_orders_1('#skF_5', k1_orders_1(u1_struct_0('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.21/1.32  tff(c_44, plain, (![A_46, B_47]: (m2_orders_2('#skF_3'(A_46, B_47), A_46, B_47) | ~m1_orders_1(B_47, k1_orders_1(u1_struct_0(A_46))) | ~l1_orders_2(A_46) | ~v5_orders_2(A_46) | ~v4_orders_2(A_46) | ~v3_orders_2(A_46) | v2_struct_0(A_46))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.21/1.32  tff(c_46, plain, (m2_orders_2('#skF_3'('#skF_4', '#skF_5'), '#skF_4', '#skF_5') | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_26, c_44])).
% 2.21/1.32  tff(c_49, plain, (m2_orders_2('#skF_3'('#skF_4', '#skF_5'), '#skF_4', '#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_30, c_28, c_46])).
% 2.21/1.32  tff(c_50, plain, (m2_orders_2('#skF_3'('#skF_4', '#skF_5'), '#skF_4', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_36, c_49])).
% 2.21/1.32  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.21/1.32  tff(c_24, plain, (k3_tarski(k4_orders_2('#skF_4', '#skF_5'))=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.21/1.32  tff(c_51, plain, (![D_48, A_49, B_50]: (r2_hidden(D_48, k4_orders_2(A_49, B_50)) | ~m2_orders_2(D_48, A_49, B_50) | ~m1_orders_1(B_50, k1_orders_1(u1_struct_0(A_49))) | ~l1_orders_2(A_49) | ~v5_orders_2(A_49) | ~v4_orders_2(A_49) | ~v3_orders_2(A_49) | v2_struct_0(A_49))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.21/1.32  tff(c_53, plain, (![D_48]: (r2_hidden(D_48, k4_orders_2('#skF_4', '#skF_5')) | ~m2_orders_2(D_48, '#skF_4', '#skF_5') | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_26, c_51])).
% 2.21/1.32  tff(c_56, plain, (![D_48]: (r2_hidden(D_48, k4_orders_2('#skF_4', '#skF_5')) | ~m2_orders_2(D_48, '#skF_4', '#skF_5') | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_30, c_28, c_53])).
% 2.21/1.32  tff(c_58, plain, (![D_51]: (r2_hidden(D_51, k4_orders_2('#skF_4', '#skF_5')) | ~m2_orders_2(D_51, '#skF_4', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_36, c_56])).
% 2.21/1.32  tff(c_4, plain, (![C_4, B_3, A_2]: (r1_tarski(C_4, B_3) | ~r2_hidden(C_4, A_2) | ~r1_tarski(k3_tarski(A_2), B_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.21/1.32  tff(c_60, plain, (![D_51, B_3]: (r1_tarski(D_51, B_3) | ~r1_tarski(k3_tarski(k4_orders_2('#skF_4', '#skF_5')), B_3) | ~m2_orders_2(D_51, '#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_58, c_4])).
% 2.21/1.32  tff(c_68, plain, (![D_52, B_53]: (r1_tarski(D_52, B_53) | ~m2_orders_2(D_52, '#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_24, c_60])).
% 2.21/1.32  tff(c_71, plain, (![B_53]: (r1_tarski('#skF_3'('#skF_4', '#skF_5'), B_53))), inference(resolution, [status(thm)], [c_50, c_68])).
% 2.21/1.32  tff(c_81, plain, (![B_59, A_60, C_61]: (r2_hidden(k1_funct_1(B_59, u1_struct_0(A_60)), C_61) | ~m2_orders_2(C_61, A_60, B_59) | ~m1_orders_1(B_59, k1_orders_1(u1_struct_0(A_60))) | ~l1_orders_2(A_60) | ~v5_orders_2(A_60) | ~v4_orders_2(A_60) | ~v3_orders_2(A_60) | v2_struct_0(A_60))), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.21/1.32  tff(c_6, plain, (![B_6, A_5]: (~r1_tarski(B_6, A_5) | ~r2_hidden(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.21/1.32  tff(c_98, plain, (![C_65, B_66, A_67]: (~r1_tarski(C_65, k1_funct_1(B_66, u1_struct_0(A_67))) | ~m2_orders_2(C_65, A_67, B_66) | ~m1_orders_1(B_66, k1_orders_1(u1_struct_0(A_67))) | ~l1_orders_2(A_67) | ~v5_orders_2(A_67) | ~v4_orders_2(A_67) | ~v3_orders_2(A_67) | v2_struct_0(A_67))), inference(resolution, [status(thm)], [c_81, c_6])).
% 2.21/1.32  tff(c_117, plain, (![A_70, B_71]: (~m2_orders_2('#skF_3'('#skF_4', '#skF_5'), A_70, B_71) | ~m1_orders_1(B_71, k1_orders_1(u1_struct_0(A_70))) | ~l1_orders_2(A_70) | ~v5_orders_2(A_70) | ~v4_orders_2(A_70) | ~v3_orders_2(A_70) | v2_struct_0(A_70))), inference(resolution, [status(thm)], [c_71, c_98])).
% 2.21/1.32  tff(c_120, plain, (~m2_orders_2('#skF_3'('#skF_4', '#skF_5'), '#skF_4', '#skF_5') | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_26, c_117])).
% 2.21/1.32  tff(c_123, plain, (v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_30, c_28, c_50, c_120])).
% 2.21/1.32  tff(c_125, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36, c_123])).
% 2.21/1.32  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.21/1.32  
% 2.21/1.32  Inference rules
% 2.21/1.32  ----------------------
% 2.21/1.32  #Ref     : 0
% 2.21/1.32  #Sup     : 16
% 2.21/1.32  #Fact    : 0
% 2.21/1.32  #Define  : 0
% 2.21/1.32  #Split   : 0
% 2.21/1.32  #Chain   : 0
% 2.21/1.32  #Close   : 0
% 2.21/1.32  
% 2.21/1.32  Ordering : KBO
% 2.21/1.32  
% 2.21/1.32  Simplification rules
% 2.21/1.32  ----------------------
% 2.21/1.32  #Subsume      : 0
% 2.21/1.32  #Demod        : 24
% 2.21/1.32  #Tautology    : 3
% 2.21/1.32  #SimpNegUnit  : 5
% 2.21/1.32  #BackRed      : 0
% 2.21/1.32  
% 2.21/1.32  #Partial instantiations: 0
% 2.21/1.32  #Strategies tried      : 1
% 2.21/1.32  
% 2.21/1.32  Timing (in seconds)
% 2.21/1.32  ----------------------
% 2.21/1.32  Preprocessing        : 0.34
% 2.21/1.32  Parsing              : 0.18
% 2.21/1.32  CNF conversion       : 0.03
% 2.21/1.32  Main loop            : 0.16
% 2.21/1.32  Inferencing          : 0.06
% 2.21/1.32  Reduction            : 0.05
% 2.21/1.32  Demodulation         : 0.03
% 2.21/1.32  BG Simplification    : 0.01
% 2.21/1.32  Subsumption          : 0.03
% 2.21/1.32  Abstraction          : 0.01
% 2.21/1.32  MUC search           : 0.00
% 2.21/1.32  Cooper               : 0.00
% 2.21/1.32  Total                : 0.53
% 2.21/1.32  Index Insertion      : 0.00
% 2.21/1.32  Index Deletion       : 0.00
% 2.21/1.32  Index Matching       : 0.00
% 2.21/1.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
