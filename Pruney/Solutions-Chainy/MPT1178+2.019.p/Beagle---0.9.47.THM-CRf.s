%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:04 EST 2020

% Result     : Theorem 2.73s
% Output     : CNFRefutation 2.73s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 125 expanded)
%              Number of leaves         :   35 (  63 expanded)
%              Depth                    :   10
%              Number of atoms          :  155 ( 374 expanded)
%              Number of equality atoms :    7 (  31 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m2_orders_2 > r2_hidden > r1_tarski > m1_subset_1 > m1_orders_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_orders_2 > k4_orders_2 > k1_funct_1 > #nlpp > u1_struct_0 > k3_tarski > k1_orders_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_4 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k4_orders_2,type,(
    k4_orders_2: ( $i * $i ) > $i )).

tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v3_orders_2,type,(
    v3_orders_2: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(m1_orders_1,type,(
    m1_orders_1: ( $i * $i ) > $o )).

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_126,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v3_orders_2(A)
          & v4_orders_2(A)
          & v5_orders_2(A)
          & l1_orders_2(A) )
       => ! [B] :
            ( m1_orders_1(B,k1_orders_1(u1_struct_0(A)))
           => k3_tarski(k4_orders_2(A,B)) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_orders_2)).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_108,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_orders_2)).

tff(f_51,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_40,axiom,(
    ! [A] :
    ? [B] : m1_subset_1(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_subset_1)).

tff(f_89,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A)
        & m1_orders_1(B,k1_orders_1(u1_struct_0(A))) )
     => ~ v1_xboole_0(k4_orders_2(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_orders_2)).

tff(f_46,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(A,k3_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l49_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_73,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d17_orders_2)).

tff(c_46,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_44,plain,(
    v3_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_42,plain,(
    v4_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_40,plain,(
    v5_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_38,plain,(
    l1_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_36,plain,(
    m1_orders_1('#skF_5',k1_orders_1(u1_struct_0('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_8,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_286,plain,(
    ! [B_85,A_86,C_87] :
      ( r2_hidden(k1_funct_1(B_85,u1_struct_0(A_86)),C_87)
      | ~ m2_orders_2(C_87,A_86,B_85)
      | ~ m1_orders_1(B_85,k1_orders_1(u1_struct_0(A_86)))
      | ~ l1_orders_2(A_86)
      | ~ v5_orders_2(A_86)
      | ~ v4_orders_2(A_86)
      | ~ v3_orders_2(A_86)
      | v2_struct_0(A_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_16,plain,(
    ! [B_11,A_10] :
      ( ~ r1_tarski(B_11,A_10)
      | ~ r2_hidden(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_370,plain,(
    ! [C_96,B_97,A_98] :
      ( ~ r1_tarski(C_96,k1_funct_1(B_97,u1_struct_0(A_98)))
      | ~ m2_orders_2(C_96,A_98,B_97)
      | ~ m1_orders_1(B_97,k1_orders_1(u1_struct_0(A_98)))
      | ~ l1_orders_2(A_98)
      | ~ v5_orders_2(A_98)
      | ~ v4_orders_2(A_98)
      | ~ v3_orders_2(A_98)
      | v2_struct_0(A_98) ) ),
    inference(resolution,[status(thm)],[c_286,c_16])).

tff(c_381,plain,(
    ! [A_99,B_100] :
      ( ~ m2_orders_2(k1_xboole_0,A_99,B_100)
      | ~ m1_orders_1(B_100,k1_orders_1(u1_struct_0(A_99)))
      | ~ l1_orders_2(A_99)
      | ~ v5_orders_2(A_99)
      | ~ v4_orders_2(A_99)
      | ~ v3_orders_2(A_99)
      | v2_struct_0(A_99) ) ),
    inference(resolution,[status(thm)],[c_8,c_370])).

tff(c_384,plain,
    ( ~ m2_orders_2(k1_xboole_0,'#skF_4','#skF_5')
    | ~ l1_orders_2('#skF_4')
    | ~ v5_orders_2('#skF_4')
    | ~ v4_orders_2('#skF_4')
    | ~ v3_orders_2('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_381])).

tff(c_387,plain,
    ( ~ m2_orders_2(k1_xboole_0,'#skF_4','#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_40,c_38,c_384])).

tff(c_388,plain,(
    ~ m2_orders_2(k1_xboole_0,'#skF_4','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_387])).

tff(c_12,plain,(
    ! [A_6] : m1_subset_1('#skF_1'(A_6),A_6) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_91,plain,(
    ! [A_56,B_57] :
      ( ~ v1_xboole_0(k4_orders_2(A_56,B_57))
      | ~ m1_orders_1(B_57,k1_orders_1(u1_struct_0(A_56)))
      | ~ l1_orders_2(A_56)
      | ~ v5_orders_2(A_56)
      | ~ v4_orders_2(A_56)
      | ~ v3_orders_2(A_56)
      | v2_struct_0(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_94,plain,
    ( ~ v1_xboole_0(k4_orders_2('#skF_4','#skF_5'))
    | ~ l1_orders_2('#skF_4')
    | ~ v5_orders_2('#skF_4')
    | ~ v4_orders_2('#skF_4')
    | ~ v3_orders_2('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_91])).

tff(c_97,plain,
    ( ~ v1_xboole_0(k4_orders_2('#skF_4','#skF_5'))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_40,c_38,c_94])).

tff(c_98,plain,(
    ~ v1_xboole_0(k4_orders_2('#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_97])).

tff(c_14,plain,(
    ! [A_8,B_9] :
      ( r2_hidden(A_8,B_9)
      | v1_xboole_0(B_9)
      | ~ m1_subset_1(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_34,plain,(
    k3_tarski(k4_orders_2('#skF_4','#skF_5')) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_56,plain,(
    ! [A_49,B_50] :
      ( r1_tarski(A_49,k3_tarski(B_50))
      | ~ r2_hidden(A_49,B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_129,plain,(
    ! [A_63] :
      ( r1_tarski(A_63,k1_xboole_0)
      | ~ r2_hidden(A_63,k4_orders_2('#skF_4','#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_56])).

tff(c_133,plain,(
    ! [A_8] :
      ( r1_tarski(A_8,k1_xboole_0)
      | v1_xboole_0(k4_orders_2('#skF_4','#skF_5'))
      | ~ m1_subset_1(A_8,k4_orders_2('#skF_4','#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_14,c_129])).

tff(c_137,plain,(
    ! [A_64] :
      ( r1_tarski(A_64,k1_xboole_0)
      | ~ m1_subset_1(A_64,k4_orders_2('#skF_4','#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_98,c_133])).

tff(c_142,plain,(
    r1_tarski('#skF_1'(k4_orders_2('#skF_4','#skF_5')),k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_12,c_137])).

tff(c_65,plain,(
    ! [B_53,A_54] :
      ( B_53 = A_54
      | ~ r1_tarski(B_53,A_54)
      | ~ r1_tarski(A_54,B_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_73,plain,(
    ! [A_3] :
      ( k1_xboole_0 = A_3
      | ~ r1_tarski(A_3,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_8,c_65])).

tff(c_157,plain,(
    '#skF_1'(k4_orders_2('#skF_4','#skF_5')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_142,c_73])).

tff(c_166,plain,(
    m1_subset_1(k1_xboole_0,k4_orders_2('#skF_4','#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_157,c_12])).

tff(c_143,plain,(
    ! [D_65,A_66,B_67] :
      ( m2_orders_2(D_65,A_66,B_67)
      | ~ r2_hidden(D_65,k4_orders_2(A_66,B_67))
      | ~ m1_orders_1(B_67,k1_orders_1(u1_struct_0(A_66)))
      | ~ l1_orders_2(A_66)
      | ~ v5_orders_2(A_66)
      | ~ v4_orders_2(A_66)
      | ~ v3_orders_2(A_66)
      | v2_struct_0(A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_408,plain,(
    ! [A_110,A_111,B_112] :
      ( m2_orders_2(A_110,A_111,B_112)
      | ~ m1_orders_1(B_112,k1_orders_1(u1_struct_0(A_111)))
      | ~ l1_orders_2(A_111)
      | ~ v5_orders_2(A_111)
      | ~ v4_orders_2(A_111)
      | ~ v3_orders_2(A_111)
      | v2_struct_0(A_111)
      | v1_xboole_0(k4_orders_2(A_111,B_112))
      | ~ m1_subset_1(A_110,k4_orders_2(A_111,B_112)) ) ),
    inference(resolution,[status(thm)],[c_14,c_143])).

tff(c_410,plain,(
    ! [A_110] :
      ( m2_orders_2(A_110,'#skF_4','#skF_5')
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4')
      | ~ v4_orders_2('#skF_4')
      | ~ v3_orders_2('#skF_4')
      | v2_struct_0('#skF_4')
      | v1_xboole_0(k4_orders_2('#skF_4','#skF_5'))
      | ~ m1_subset_1(A_110,k4_orders_2('#skF_4','#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_36,c_408])).

tff(c_413,plain,(
    ! [A_110] :
      ( m2_orders_2(A_110,'#skF_4','#skF_5')
      | v2_struct_0('#skF_4')
      | v1_xboole_0(k4_orders_2('#skF_4','#skF_5'))
      | ~ m1_subset_1(A_110,k4_orders_2('#skF_4','#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_40,c_38,c_410])).

tff(c_415,plain,(
    ! [A_113] :
      ( m2_orders_2(A_113,'#skF_4','#skF_5')
      | ~ m1_subset_1(A_113,k4_orders_2('#skF_4','#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_98,c_46,c_413])).

tff(c_418,plain,(
    m2_orders_2(k1_xboole_0,'#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_166,c_415])).

tff(c_426,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_388,c_418])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:48:38 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.73/1.46  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.73/1.46  
% 2.73/1.46  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.73/1.47  %$ m2_orders_2 > r2_hidden > r1_tarski > m1_subset_1 > m1_orders_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_orders_2 > k4_orders_2 > k1_funct_1 > #nlpp > u1_struct_0 > k3_tarski > k1_orders_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_4 > #skF_3
% 2.73/1.47  
% 2.73/1.47  %Foreground sorts:
% 2.73/1.47  
% 2.73/1.47  
% 2.73/1.47  %Background operators:
% 2.73/1.47  
% 2.73/1.47  
% 2.73/1.47  %Foreground operators:
% 2.73/1.47  tff(k4_orders_2, type, k4_orders_2: ($i * $i) > $i).
% 2.73/1.47  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.73/1.47  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 2.73/1.47  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.73/1.47  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.73/1.47  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.73/1.47  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.73/1.47  tff(m1_orders_1, type, m1_orders_1: ($i * $i) > $o).
% 2.73/1.47  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.73/1.47  tff(m2_orders_2, type, m2_orders_2: ($i * $i * $i) > $o).
% 2.73/1.47  tff('#skF_5', type, '#skF_5': $i).
% 2.73/1.47  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.73/1.47  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 2.73/1.47  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 2.73/1.47  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.73/1.47  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.73/1.47  tff(k1_orders_1, type, k1_orders_1: $i > $i).
% 2.73/1.47  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.73/1.47  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.73/1.47  tff('#skF_4', type, '#skF_4': $i).
% 2.73/1.47  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.73/1.47  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.73/1.47  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.73/1.47  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.73/1.47  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.73/1.47  
% 2.73/1.48  tff(f_126, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => ~(k3_tarski(k4_orders_2(A, B)) = k1_xboole_0))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_orders_2)).
% 2.73/1.48  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.73/1.48  tff(f_108, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: (m2_orders_2(C, A, B) => r2_hidden(k1_funct_1(B, u1_struct_0(A)), C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_orders_2)).
% 2.73/1.48  tff(f_51, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 2.73/1.48  tff(f_40, axiom, (![A]: (?[B]: m1_subset_1(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', existence_m1_subset_1)).
% 2.73/1.48  tff(f_89, axiom, (![A, B]: ((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) & m1_orders_1(B, k1_orders_1(u1_struct_0(A)))) => ~v1_xboole_0(k4_orders_2(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc9_orders_2)).
% 2.73/1.48  tff(f_46, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 2.73/1.48  tff(f_37, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(A, k3_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l49_zfmisc_1)).
% 2.73/1.48  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.73/1.48  tff(f_73, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: ((C = k4_orders_2(A, B)) <=> (![D]: (r2_hidden(D, C) <=> m2_orders_2(D, A, B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d17_orders_2)).
% 2.73/1.48  tff(c_46, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_126])).
% 2.73/1.48  tff(c_44, plain, (v3_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_126])).
% 2.73/1.48  tff(c_42, plain, (v4_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_126])).
% 2.73/1.48  tff(c_40, plain, (v5_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_126])).
% 2.73/1.48  tff(c_38, plain, (l1_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_126])).
% 2.73/1.48  tff(c_36, plain, (m1_orders_1('#skF_5', k1_orders_1(u1_struct_0('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_126])).
% 2.73/1.48  tff(c_8, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.73/1.48  tff(c_286, plain, (![B_85, A_86, C_87]: (r2_hidden(k1_funct_1(B_85, u1_struct_0(A_86)), C_87) | ~m2_orders_2(C_87, A_86, B_85) | ~m1_orders_1(B_85, k1_orders_1(u1_struct_0(A_86))) | ~l1_orders_2(A_86) | ~v5_orders_2(A_86) | ~v4_orders_2(A_86) | ~v3_orders_2(A_86) | v2_struct_0(A_86))), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.73/1.48  tff(c_16, plain, (![B_11, A_10]: (~r1_tarski(B_11, A_10) | ~r2_hidden(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.73/1.48  tff(c_370, plain, (![C_96, B_97, A_98]: (~r1_tarski(C_96, k1_funct_1(B_97, u1_struct_0(A_98))) | ~m2_orders_2(C_96, A_98, B_97) | ~m1_orders_1(B_97, k1_orders_1(u1_struct_0(A_98))) | ~l1_orders_2(A_98) | ~v5_orders_2(A_98) | ~v4_orders_2(A_98) | ~v3_orders_2(A_98) | v2_struct_0(A_98))), inference(resolution, [status(thm)], [c_286, c_16])).
% 2.73/1.48  tff(c_381, plain, (![A_99, B_100]: (~m2_orders_2(k1_xboole_0, A_99, B_100) | ~m1_orders_1(B_100, k1_orders_1(u1_struct_0(A_99))) | ~l1_orders_2(A_99) | ~v5_orders_2(A_99) | ~v4_orders_2(A_99) | ~v3_orders_2(A_99) | v2_struct_0(A_99))), inference(resolution, [status(thm)], [c_8, c_370])).
% 2.73/1.48  tff(c_384, plain, (~m2_orders_2(k1_xboole_0, '#skF_4', '#skF_5') | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_36, c_381])).
% 2.73/1.48  tff(c_387, plain, (~m2_orders_2(k1_xboole_0, '#skF_4', '#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_40, c_38, c_384])).
% 2.73/1.48  tff(c_388, plain, (~m2_orders_2(k1_xboole_0, '#skF_4', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_46, c_387])).
% 2.73/1.48  tff(c_12, plain, (![A_6]: (m1_subset_1('#skF_1'(A_6), A_6))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.73/1.48  tff(c_91, plain, (![A_56, B_57]: (~v1_xboole_0(k4_orders_2(A_56, B_57)) | ~m1_orders_1(B_57, k1_orders_1(u1_struct_0(A_56))) | ~l1_orders_2(A_56) | ~v5_orders_2(A_56) | ~v4_orders_2(A_56) | ~v3_orders_2(A_56) | v2_struct_0(A_56))), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.73/1.48  tff(c_94, plain, (~v1_xboole_0(k4_orders_2('#skF_4', '#skF_5')) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_36, c_91])).
% 2.73/1.48  tff(c_97, plain, (~v1_xboole_0(k4_orders_2('#skF_4', '#skF_5')) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_40, c_38, c_94])).
% 2.73/1.48  tff(c_98, plain, (~v1_xboole_0(k4_orders_2('#skF_4', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_46, c_97])).
% 2.73/1.48  tff(c_14, plain, (![A_8, B_9]: (r2_hidden(A_8, B_9) | v1_xboole_0(B_9) | ~m1_subset_1(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.73/1.48  tff(c_34, plain, (k3_tarski(k4_orders_2('#skF_4', '#skF_5'))=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_126])).
% 2.73/1.48  tff(c_56, plain, (![A_49, B_50]: (r1_tarski(A_49, k3_tarski(B_50)) | ~r2_hidden(A_49, B_50))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.73/1.48  tff(c_129, plain, (![A_63]: (r1_tarski(A_63, k1_xboole_0) | ~r2_hidden(A_63, k4_orders_2('#skF_4', '#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_34, c_56])).
% 2.73/1.48  tff(c_133, plain, (![A_8]: (r1_tarski(A_8, k1_xboole_0) | v1_xboole_0(k4_orders_2('#skF_4', '#skF_5')) | ~m1_subset_1(A_8, k4_orders_2('#skF_4', '#skF_5')))), inference(resolution, [status(thm)], [c_14, c_129])).
% 2.73/1.48  tff(c_137, plain, (![A_64]: (r1_tarski(A_64, k1_xboole_0) | ~m1_subset_1(A_64, k4_orders_2('#skF_4', '#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_98, c_133])).
% 2.73/1.48  tff(c_142, plain, (r1_tarski('#skF_1'(k4_orders_2('#skF_4', '#skF_5')), k1_xboole_0)), inference(resolution, [status(thm)], [c_12, c_137])).
% 2.73/1.48  tff(c_65, plain, (![B_53, A_54]: (B_53=A_54 | ~r1_tarski(B_53, A_54) | ~r1_tarski(A_54, B_53))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.73/1.48  tff(c_73, plain, (![A_3]: (k1_xboole_0=A_3 | ~r1_tarski(A_3, k1_xboole_0))), inference(resolution, [status(thm)], [c_8, c_65])).
% 2.73/1.48  tff(c_157, plain, ('#skF_1'(k4_orders_2('#skF_4', '#skF_5'))=k1_xboole_0), inference(resolution, [status(thm)], [c_142, c_73])).
% 2.73/1.48  tff(c_166, plain, (m1_subset_1(k1_xboole_0, k4_orders_2('#skF_4', '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_157, c_12])).
% 2.73/1.48  tff(c_143, plain, (![D_65, A_66, B_67]: (m2_orders_2(D_65, A_66, B_67) | ~r2_hidden(D_65, k4_orders_2(A_66, B_67)) | ~m1_orders_1(B_67, k1_orders_1(u1_struct_0(A_66))) | ~l1_orders_2(A_66) | ~v5_orders_2(A_66) | ~v4_orders_2(A_66) | ~v3_orders_2(A_66) | v2_struct_0(A_66))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.73/1.48  tff(c_408, plain, (![A_110, A_111, B_112]: (m2_orders_2(A_110, A_111, B_112) | ~m1_orders_1(B_112, k1_orders_1(u1_struct_0(A_111))) | ~l1_orders_2(A_111) | ~v5_orders_2(A_111) | ~v4_orders_2(A_111) | ~v3_orders_2(A_111) | v2_struct_0(A_111) | v1_xboole_0(k4_orders_2(A_111, B_112)) | ~m1_subset_1(A_110, k4_orders_2(A_111, B_112)))), inference(resolution, [status(thm)], [c_14, c_143])).
% 2.73/1.48  tff(c_410, plain, (![A_110]: (m2_orders_2(A_110, '#skF_4', '#skF_5') | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4') | v1_xboole_0(k4_orders_2('#skF_4', '#skF_5')) | ~m1_subset_1(A_110, k4_orders_2('#skF_4', '#skF_5')))), inference(resolution, [status(thm)], [c_36, c_408])).
% 2.73/1.48  tff(c_413, plain, (![A_110]: (m2_orders_2(A_110, '#skF_4', '#skF_5') | v2_struct_0('#skF_4') | v1_xboole_0(k4_orders_2('#skF_4', '#skF_5')) | ~m1_subset_1(A_110, k4_orders_2('#skF_4', '#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_40, c_38, c_410])).
% 2.73/1.48  tff(c_415, plain, (![A_113]: (m2_orders_2(A_113, '#skF_4', '#skF_5') | ~m1_subset_1(A_113, k4_orders_2('#skF_4', '#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_98, c_46, c_413])).
% 2.73/1.48  tff(c_418, plain, (m2_orders_2(k1_xboole_0, '#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_166, c_415])).
% 2.73/1.48  tff(c_426, plain, $false, inference(negUnitSimplification, [status(thm)], [c_388, c_418])).
% 2.73/1.48  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.73/1.48  
% 2.73/1.48  Inference rules
% 2.73/1.48  ----------------------
% 2.73/1.48  #Ref     : 0
% 2.73/1.48  #Sup     : 70
% 2.73/1.48  #Fact    : 0
% 2.73/1.48  #Define  : 0
% 2.73/1.48  #Split   : 2
% 2.73/1.48  #Chain   : 0
% 2.73/1.48  #Close   : 0
% 2.73/1.48  
% 2.73/1.48  Ordering : KBO
% 2.73/1.48  
% 2.73/1.48  Simplification rules
% 2.73/1.48  ----------------------
% 2.73/1.48  #Subsume      : 9
% 2.73/1.48  #Demod        : 50
% 2.73/1.48  #Tautology    : 18
% 2.73/1.48  #SimpNegUnit  : 14
% 2.73/1.48  #BackRed      : 1
% 2.73/1.48  
% 2.73/1.48  #Partial instantiations: 0
% 2.73/1.48  #Strategies tried      : 1
% 2.73/1.48  
% 2.73/1.48  Timing (in seconds)
% 2.73/1.48  ----------------------
% 2.73/1.48  Preprocessing        : 0.37
% 2.73/1.48  Parsing              : 0.22
% 2.73/1.49  CNF conversion       : 0.03
% 2.73/1.49  Main loop            : 0.33
% 2.73/1.49  Inferencing          : 0.13
% 2.73/1.49  Reduction            : 0.09
% 2.73/1.49  Demodulation         : 0.06
% 2.73/1.49  BG Simplification    : 0.02
% 2.73/1.49  Subsumption          : 0.07
% 2.73/1.49  Abstraction          : 0.01
% 2.73/1.49  MUC search           : 0.00
% 2.73/1.49  Cooper               : 0.00
% 2.73/1.49  Total                : 0.74
% 2.73/1.49  Index Insertion      : 0.00
% 2.73/1.49  Index Deletion       : 0.00
% 2.73/1.49  Index Matching       : 0.00
% 2.73/1.49  BG Taut test         : 0.00
%------------------------------------------------------------------------------
