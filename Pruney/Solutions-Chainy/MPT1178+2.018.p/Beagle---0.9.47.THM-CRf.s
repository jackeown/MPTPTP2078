%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:04 EST 2020

% Result     : Theorem 5.64s
% Output     : CNFRefutation 5.64s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 131 expanded)
%              Number of leaves         :   38 (  66 expanded)
%              Depth                    :   11
%              Number of atoms          :  164 ( 383 expanded)
%              Number of equality atoms :   14 (  38 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m2_orders_2 > r2_hidden > r1_tarski > m1_subset_1 > m1_orders_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_orders_2 > k4_orders_2 > k1_funct_1 > #nlpp > u1_struct_0 > k3_tarski > k1_tarski > k1_orders_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_4 > #skF_3

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

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

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

tff(f_132,negated_conjecture,(
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

tff(f_46,axiom,(
    ! [A] :
    ? [B] : m1_subset_1(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_subset_1)).

tff(f_95,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A)
        & m1_orders_1(B,k1_orders_1(u1_struct_0(A))) )
     => ~ v1_xboole_0(k4_orders_2(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_orders_2)).

tff(f_52,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_39,axiom,(
    ! [A] : k3_tarski(k1_tarski(A)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_zfmisc_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => r1_tarski(k3_tarski(A),k3_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_zfmisc_1)).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_79,axiom,(
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

tff(f_114,axiom,(
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

tff(f_57,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_52,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_50,plain,(
    v3_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_48,plain,(
    v4_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_46,plain,(
    v5_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_44,plain,(
    l1_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_18,plain,(
    ! [A_9] : m1_subset_1('#skF_1'(A_9),A_9) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_42,plain,(
    m1_orders_1('#skF_5',k1_orders_1(u1_struct_0('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_193,plain,(
    ! [A_72,B_73] :
      ( ~ v1_xboole_0(k4_orders_2(A_72,B_73))
      | ~ m1_orders_1(B_73,k1_orders_1(u1_struct_0(A_72)))
      | ~ l1_orders_2(A_72)
      | ~ v5_orders_2(A_72)
      | ~ v4_orders_2(A_72)
      | ~ v3_orders_2(A_72)
      | v2_struct_0(A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_196,plain,
    ( ~ v1_xboole_0(k4_orders_2('#skF_4','#skF_5'))
    | ~ l1_orders_2('#skF_4')
    | ~ v5_orders_2('#skF_4')
    | ~ v4_orders_2('#skF_4')
    | ~ v3_orders_2('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_42,c_193])).

tff(c_199,plain,
    ( ~ v1_xboole_0(k4_orders_2('#skF_4','#skF_5'))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_44,c_196])).

tff(c_200,plain,(
    ~ v1_xboole_0(k4_orders_2('#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_199])).

tff(c_20,plain,(
    ! [A_11,B_12] :
      ( r2_hidden(A_11,B_12)
      | v1_xboole_0(B_12)
      | ~ m1_subset_1(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_14,plain,(
    ! [A_6] : k3_tarski(k1_tarski(A_6)) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_12,plain,(
    ! [A_4,B_5] :
      ( r1_tarski(k1_tarski(A_4),B_5)
      | ~ r2_hidden(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_40,plain,(
    k3_tarski(k4_orders_2('#skF_4','#skF_5')) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_87,plain,(
    ! [A_58,B_59] :
      ( r1_tarski(k3_tarski(A_58),k3_tarski(B_59))
      | ~ r1_tarski(A_58,B_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_93,plain,(
    ! [A_58] :
      ( r1_tarski(k3_tarski(A_58),k1_xboole_0)
      | ~ r1_tarski(A_58,k4_orders_2('#skF_4','#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_87])).

tff(c_8,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_108,plain,(
    ! [B_62,A_63] :
      ( B_62 = A_63
      | ~ r1_tarski(B_62,A_63)
      | ~ r1_tarski(A_63,B_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_138,plain,(
    ! [A_65] :
      ( k1_xboole_0 = A_65
      | ~ r1_tarski(A_65,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_8,c_108])).

tff(c_246,plain,(
    ! [A_75] :
      ( k3_tarski(A_75) = k1_xboole_0
      | ~ r1_tarski(A_75,k4_orders_2('#skF_4','#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_93,c_138])).

tff(c_254,plain,(
    ! [A_4] :
      ( k3_tarski(k1_tarski(A_4)) = k1_xboole_0
      | ~ r2_hidden(A_4,k4_orders_2('#skF_4','#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_12,c_246])).

tff(c_282,plain,(
    ! [A_77] :
      ( k1_xboole_0 = A_77
      | ~ r2_hidden(A_77,k4_orders_2('#skF_4','#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_254])).

tff(c_286,plain,(
    ! [A_11] :
      ( k1_xboole_0 = A_11
      | v1_xboole_0(k4_orders_2('#skF_4','#skF_5'))
      | ~ m1_subset_1(A_11,k4_orders_2('#skF_4','#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_20,c_282])).

tff(c_355,plain,(
    ! [A_84] :
      ( k1_xboole_0 = A_84
      | ~ m1_subset_1(A_84,k4_orders_2('#skF_4','#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_200,c_286])).

tff(c_360,plain,(
    '#skF_1'(k4_orders_2('#skF_4','#skF_5')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_18,c_355])).

tff(c_350,plain,(
    ! [D_81,A_82,B_83] :
      ( m2_orders_2(D_81,A_82,B_83)
      | ~ r2_hidden(D_81,k4_orders_2(A_82,B_83))
      | ~ m1_orders_1(B_83,k1_orders_1(u1_struct_0(A_82)))
      | ~ l1_orders_2(A_82)
      | ~ v5_orders_2(A_82)
      | ~ v4_orders_2(A_82)
      | ~ v3_orders_2(A_82)
      | v2_struct_0(A_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_1750,plain,(
    ! [A_187,A_188,B_189] :
      ( m2_orders_2(A_187,A_188,B_189)
      | ~ m1_orders_1(B_189,k1_orders_1(u1_struct_0(A_188)))
      | ~ l1_orders_2(A_188)
      | ~ v5_orders_2(A_188)
      | ~ v4_orders_2(A_188)
      | ~ v3_orders_2(A_188)
      | v2_struct_0(A_188)
      | v1_xboole_0(k4_orders_2(A_188,B_189))
      | ~ m1_subset_1(A_187,k4_orders_2(A_188,B_189)) ) ),
    inference(resolution,[status(thm)],[c_20,c_350])).

tff(c_1752,plain,(
    ! [A_187] :
      ( m2_orders_2(A_187,'#skF_4','#skF_5')
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4')
      | ~ v4_orders_2('#skF_4')
      | ~ v3_orders_2('#skF_4')
      | v2_struct_0('#skF_4')
      | v1_xboole_0(k4_orders_2('#skF_4','#skF_5'))
      | ~ m1_subset_1(A_187,k4_orders_2('#skF_4','#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_42,c_1750])).

tff(c_1755,plain,(
    ! [A_187] :
      ( m2_orders_2(A_187,'#skF_4','#skF_5')
      | v2_struct_0('#skF_4')
      | v1_xboole_0(k4_orders_2('#skF_4','#skF_5'))
      | ~ m1_subset_1(A_187,k4_orders_2('#skF_4','#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_44,c_1752])).

tff(c_1757,plain,(
    ! [A_190] :
      ( m2_orders_2(A_190,'#skF_4','#skF_5')
      | ~ m1_subset_1(A_190,k4_orders_2('#skF_4','#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_200,c_52,c_1755])).

tff(c_1764,plain,(
    m2_orders_2('#skF_1'(k4_orders_2('#skF_4','#skF_5')),'#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_18,c_1757])).

tff(c_1767,plain,(
    m2_orders_2(k1_xboole_0,'#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_360,c_1764])).

tff(c_557,plain,(
    ! [B_102,A_103,C_104] :
      ( r2_hidden(k1_funct_1(B_102,u1_struct_0(A_103)),C_104)
      | ~ m2_orders_2(C_104,A_103,B_102)
      | ~ m1_orders_1(B_102,k1_orders_1(u1_struct_0(A_103)))
      | ~ l1_orders_2(A_103)
      | ~ v5_orders_2(A_103)
      | ~ v4_orders_2(A_103)
      | ~ v3_orders_2(A_103)
      | v2_struct_0(A_103) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_22,plain,(
    ! [B_14,A_13] :
      ( ~ r1_tarski(B_14,A_13)
      | ~ r2_hidden(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_1493,plain,(
    ! [C_173,B_174,A_175] :
      ( ~ r1_tarski(C_173,k1_funct_1(B_174,u1_struct_0(A_175)))
      | ~ m2_orders_2(C_173,A_175,B_174)
      | ~ m1_orders_1(B_174,k1_orders_1(u1_struct_0(A_175)))
      | ~ l1_orders_2(A_175)
      | ~ v5_orders_2(A_175)
      | ~ v4_orders_2(A_175)
      | ~ v3_orders_2(A_175)
      | v2_struct_0(A_175) ) ),
    inference(resolution,[status(thm)],[c_557,c_22])).

tff(c_3444,plain,(
    ! [A_304,B_305] :
      ( ~ m2_orders_2(k1_xboole_0,A_304,B_305)
      | ~ m1_orders_1(B_305,k1_orders_1(u1_struct_0(A_304)))
      | ~ l1_orders_2(A_304)
      | ~ v5_orders_2(A_304)
      | ~ v4_orders_2(A_304)
      | ~ v3_orders_2(A_304)
      | v2_struct_0(A_304) ) ),
    inference(resolution,[status(thm)],[c_8,c_1493])).

tff(c_3447,plain,
    ( ~ m2_orders_2(k1_xboole_0,'#skF_4','#skF_5')
    | ~ l1_orders_2('#skF_4')
    | ~ v5_orders_2('#skF_4')
    | ~ v4_orders_2('#skF_4')
    | ~ v3_orders_2('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_42,c_3444])).

tff(c_3450,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_44,c_1767,c_3447])).

tff(c_3452,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_3450])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:59:09 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.64/2.11  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.64/2.12  
% 5.64/2.12  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.64/2.12  %$ m2_orders_2 > r2_hidden > r1_tarski > m1_subset_1 > m1_orders_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > l1_orders_2 > k4_orders_2 > k1_funct_1 > #nlpp > u1_struct_0 > k3_tarski > k1_tarski > k1_orders_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_4 > #skF_3
% 5.64/2.12  
% 5.64/2.12  %Foreground sorts:
% 5.64/2.12  
% 5.64/2.12  
% 5.64/2.12  %Background operators:
% 5.64/2.12  
% 5.64/2.12  
% 5.64/2.12  %Foreground operators:
% 5.64/2.12  tff(k4_orders_2, type, k4_orders_2: ($i * $i) > $i).
% 5.64/2.12  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 5.64/2.12  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 5.64/2.12  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.64/2.12  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.64/2.12  tff(k1_tarski, type, k1_tarski: $i > $i).
% 5.64/2.12  tff('#skF_1', type, '#skF_1': $i > $i).
% 5.64/2.12  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.64/2.12  tff(m1_orders_1, type, m1_orders_1: ($i * $i) > $o).
% 5.64/2.12  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.64/2.12  tff(m2_orders_2, type, m2_orders_2: ($i * $i * $i) > $o).
% 5.64/2.12  tff('#skF_5', type, '#skF_5': $i).
% 5.64/2.12  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 5.64/2.12  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 5.64/2.12  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 5.64/2.12  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 5.64/2.12  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 5.64/2.12  tff(k1_orders_1, type, k1_orders_1: $i > $i).
% 5.64/2.12  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.64/2.12  tff(k3_tarski, type, k3_tarski: $i > $i).
% 5.64/2.12  tff('#skF_4', type, '#skF_4': $i).
% 5.64/2.12  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 5.64/2.12  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.64/2.12  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.64/2.12  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.64/2.12  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.64/2.12  
% 5.64/2.14  tff(f_132, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => ~(k3_tarski(k4_orders_2(A, B)) = k1_xboole_0))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_orders_2)).
% 5.64/2.14  tff(f_46, axiom, (![A]: (?[B]: m1_subset_1(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', existence_m1_subset_1)).
% 5.64/2.14  tff(f_95, axiom, (![A, B]: ((((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) & m1_orders_1(B, k1_orders_1(u1_struct_0(A)))) => ~v1_xboole_0(k4_orders_2(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc9_orders_2)).
% 5.64/2.14  tff(f_52, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 5.64/2.14  tff(f_39, axiom, (![A]: (k3_tarski(k1_tarski(A)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_zfmisc_1)).
% 5.64/2.14  tff(f_37, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 5.64/2.14  tff(f_43, axiom, (![A, B]: (r1_tarski(A, B) => r1_tarski(k3_tarski(A), k3_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_zfmisc_1)).
% 5.64/2.14  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 5.64/2.14  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.64/2.14  tff(f_79, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: ((C = k4_orders_2(A, B)) <=> (![D]: (r2_hidden(D, C) <=> m2_orders_2(D, A, B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d17_orders_2)).
% 5.64/2.14  tff(f_114, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_orders_1(B, k1_orders_1(u1_struct_0(A))) => (![C]: (m2_orders_2(C, A, B) => r2_hidden(k1_funct_1(B, u1_struct_0(A)), C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_orders_2)).
% 5.64/2.14  tff(f_57, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 5.64/2.14  tff(c_52, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_132])).
% 5.64/2.14  tff(c_50, plain, (v3_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_132])).
% 5.64/2.14  tff(c_48, plain, (v4_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_132])).
% 5.64/2.14  tff(c_46, plain, (v5_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_132])).
% 5.64/2.14  tff(c_44, plain, (l1_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_132])).
% 5.64/2.14  tff(c_18, plain, (![A_9]: (m1_subset_1('#skF_1'(A_9), A_9))), inference(cnfTransformation, [status(thm)], [f_46])).
% 5.64/2.14  tff(c_42, plain, (m1_orders_1('#skF_5', k1_orders_1(u1_struct_0('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_132])).
% 5.64/2.14  tff(c_193, plain, (![A_72, B_73]: (~v1_xboole_0(k4_orders_2(A_72, B_73)) | ~m1_orders_1(B_73, k1_orders_1(u1_struct_0(A_72))) | ~l1_orders_2(A_72) | ~v5_orders_2(A_72) | ~v4_orders_2(A_72) | ~v3_orders_2(A_72) | v2_struct_0(A_72))), inference(cnfTransformation, [status(thm)], [f_95])).
% 5.64/2.14  tff(c_196, plain, (~v1_xboole_0(k4_orders_2('#skF_4', '#skF_5')) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_42, c_193])).
% 5.64/2.14  tff(c_199, plain, (~v1_xboole_0(k4_orders_2('#skF_4', '#skF_5')) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_44, c_196])).
% 5.64/2.14  tff(c_200, plain, (~v1_xboole_0(k4_orders_2('#skF_4', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_52, c_199])).
% 5.64/2.14  tff(c_20, plain, (![A_11, B_12]: (r2_hidden(A_11, B_12) | v1_xboole_0(B_12) | ~m1_subset_1(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_52])).
% 5.64/2.14  tff(c_14, plain, (![A_6]: (k3_tarski(k1_tarski(A_6))=A_6)), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.64/2.14  tff(c_12, plain, (![A_4, B_5]: (r1_tarski(k1_tarski(A_4), B_5) | ~r2_hidden(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.64/2.14  tff(c_40, plain, (k3_tarski(k4_orders_2('#skF_4', '#skF_5'))=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_132])).
% 5.64/2.14  tff(c_87, plain, (![A_58, B_59]: (r1_tarski(k3_tarski(A_58), k3_tarski(B_59)) | ~r1_tarski(A_58, B_59))), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.64/2.14  tff(c_93, plain, (![A_58]: (r1_tarski(k3_tarski(A_58), k1_xboole_0) | ~r1_tarski(A_58, k4_orders_2('#skF_4', '#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_40, c_87])).
% 5.64/2.14  tff(c_8, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 5.64/2.14  tff(c_108, plain, (![B_62, A_63]: (B_62=A_63 | ~r1_tarski(B_62, A_63) | ~r1_tarski(A_63, B_62))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.64/2.14  tff(c_138, plain, (![A_65]: (k1_xboole_0=A_65 | ~r1_tarski(A_65, k1_xboole_0))), inference(resolution, [status(thm)], [c_8, c_108])).
% 5.64/2.14  tff(c_246, plain, (![A_75]: (k3_tarski(A_75)=k1_xboole_0 | ~r1_tarski(A_75, k4_orders_2('#skF_4', '#skF_5')))), inference(resolution, [status(thm)], [c_93, c_138])).
% 5.64/2.14  tff(c_254, plain, (![A_4]: (k3_tarski(k1_tarski(A_4))=k1_xboole_0 | ~r2_hidden(A_4, k4_orders_2('#skF_4', '#skF_5')))), inference(resolution, [status(thm)], [c_12, c_246])).
% 5.64/2.14  tff(c_282, plain, (![A_77]: (k1_xboole_0=A_77 | ~r2_hidden(A_77, k4_orders_2('#skF_4', '#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_254])).
% 5.64/2.14  tff(c_286, plain, (![A_11]: (k1_xboole_0=A_11 | v1_xboole_0(k4_orders_2('#skF_4', '#skF_5')) | ~m1_subset_1(A_11, k4_orders_2('#skF_4', '#skF_5')))), inference(resolution, [status(thm)], [c_20, c_282])).
% 5.64/2.14  tff(c_355, plain, (![A_84]: (k1_xboole_0=A_84 | ~m1_subset_1(A_84, k4_orders_2('#skF_4', '#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_200, c_286])).
% 5.64/2.14  tff(c_360, plain, ('#skF_1'(k4_orders_2('#skF_4', '#skF_5'))=k1_xboole_0), inference(resolution, [status(thm)], [c_18, c_355])).
% 5.64/2.14  tff(c_350, plain, (![D_81, A_82, B_83]: (m2_orders_2(D_81, A_82, B_83) | ~r2_hidden(D_81, k4_orders_2(A_82, B_83)) | ~m1_orders_1(B_83, k1_orders_1(u1_struct_0(A_82))) | ~l1_orders_2(A_82) | ~v5_orders_2(A_82) | ~v4_orders_2(A_82) | ~v3_orders_2(A_82) | v2_struct_0(A_82))), inference(cnfTransformation, [status(thm)], [f_79])).
% 5.64/2.14  tff(c_1750, plain, (![A_187, A_188, B_189]: (m2_orders_2(A_187, A_188, B_189) | ~m1_orders_1(B_189, k1_orders_1(u1_struct_0(A_188))) | ~l1_orders_2(A_188) | ~v5_orders_2(A_188) | ~v4_orders_2(A_188) | ~v3_orders_2(A_188) | v2_struct_0(A_188) | v1_xboole_0(k4_orders_2(A_188, B_189)) | ~m1_subset_1(A_187, k4_orders_2(A_188, B_189)))), inference(resolution, [status(thm)], [c_20, c_350])).
% 5.64/2.14  tff(c_1752, plain, (![A_187]: (m2_orders_2(A_187, '#skF_4', '#skF_5') | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4') | v1_xboole_0(k4_orders_2('#skF_4', '#skF_5')) | ~m1_subset_1(A_187, k4_orders_2('#skF_4', '#skF_5')))), inference(resolution, [status(thm)], [c_42, c_1750])).
% 5.64/2.14  tff(c_1755, plain, (![A_187]: (m2_orders_2(A_187, '#skF_4', '#skF_5') | v2_struct_0('#skF_4') | v1_xboole_0(k4_orders_2('#skF_4', '#skF_5')) | ~m1_subset_1(A_187, k4_orders_2('#skF_4', '#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_44, c_1752])).
% 5.64/2.14  tff(c_1757, plain, (![A_190]: (m2_orders_2(A_190, '#skF_4', '#skF_5') | ~m1_subset_1(A_190, k4_orders_2('#skF_4', '#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_200, c_52, c_1755])).
% 5.64/2.14  tff(c_1764, plain, (m2_orders_2('#skF_1'(k4_orders_2('#skF_4', '#skF_5')), '#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_18, c_1757])).
% 5.64/2.14  tff(c_1767, plain, (m2_orders_2(k1_xboole_0, '#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_360, c_1764])).
% 5.64/2.14  tff(c_557, plain, (![B_102, A_103, C_104]: (r2_hidden(k1_funct_1(B_102, u1_struct_0(A_103)), C_104) | ~m2_orders_2(C_104, A_103, B_102) | ~m1_orders_1(B_102, k1_orders_1(u1_struct_0(A_103))) | ~l1_orders_2(A_103) | ~v5_orders_2(A_103) | ~v4_orders_2(A_103) | ~v3_orders_2(A_103) | v2_struct_0(A_103))), inference(cnfTransformation, [status(thm)], [f_114])).
% 5.64/2.14  tff(c_22, plain, (![B_14, A_13]: (~r1_tarski(B_14, A_13) | ~r2_hidden(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_57])).
% 5.64/2.14  tff(c_1493, plain, (![C_173, B_174, A_175]: (~r1_tarski(C_173, k1_funct_1(B_174, u1_struct_0(A_175))) | ~m2_orders_2(C_173, A_175, B_174) | ~m1_orders_1(B_174, k1_orders_1(u1_struct_0(A_175))) | ~l1_orders_2(A_175) | ~v5_orders_2(A_175) | ~v4_orders_2(A_175) | ~v3_orders_2(A_175) | v2_struct_0(A_175))), inference(resolution, [status(thm)], [c_557, c_22])).
% 5.64/2.14  tff(c_3444, plain, (![A_304, B_305]: (~m2_orders_2(k1_xboole_0, A_304, B_305) | ~m1_orders_1(B_305, k1_orders_1(u1_struct_0(A_304))) | ~l1_orders_2(A_304) | ~v5_orders_2(A_304) | ~v4_orders_2(A_304) | ~v3_orders_2(A_304) | v2_struct_0(A_304))), inference(resolution, [status(thm)], [c_8, c_1493])).
% 5.64/2.14  tff(c_3447, plain, (~m2_orders_2(k1_xboole_0, '#skF_4', '#skF_5') | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_42, c_3444])).
% 5.64/2.14  tff(c_3450, plain, (v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_44, c_1767, c_3447])).
% 5.64/2.14  tff(c_3452, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_3450])).
% 5.64/2.14  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.64/2.14  
% 5.64/2.14  Inference rules
% 5.64/2.14  ----------------------
% 5.64/2.14  #Ref     : 0
% 5.64/2.14  #Sup     : 688
% 5.64/2.14  #Fact    : 0
% 5.64/2.14  #Define  : 0
% 5.64/2.14  #Split   : 6
% 5.64/2.14  #Chain   : 0
% 5.64/2.14  #Close   : 0
% 5.64/2.14  
% 5.64/2.14  Ordering : KBO
% 5.64/2.14  
% 5.64/2.14  Simplification rules
% 5.64/2.14  ----------------------
% 5.64/2.14  #Subsume      : 148
% 5.64/2.14  #Demod        : 427
% 5.64/2.14  #Tautology    : 150
% 5.64/2.14  #SimpNegUnit  : 41
% 5.64/2.14  #BackRed      : 48
% 5.64/2.14  
% 5.64/2.14  #Partial instantiations: 0
% 5.64/2.14  #Strategies tried      : 1
% 5.64/2.14  
% 5.64/2.14  Timing (in seconds)
% 5.64/2.14  ----------------------
% 5.64/2.14  Preprocessing        : 0.34
% 5.64/2.14  Parsing              : 0.18
% 5.64/2.14  CNF conversion       : 0.03
% 5.64/2.14  Main loop            : 0.97
% 5.64/2.14  Inferencing          : 0.32
% 5.64/2.14  Reduction            : 0.30
% 5.64/2.14  Demodulation         : 0.19
% 5.64/2.14  BG Simplification    : 0.04
% 5.64/2.14  Subsumption          : 0.24
% 5.64/2.14  Abstraction          : 0.04
% 5.64/2.14  MUC search           : 0.00
% 5.64/2.14  Cooper               : 0.00
% 5.64/2.14  Total                : 1.35
% 5.64/2.14  Index Insertion      : 0.00
% 5.64/2.14  Index Deletion       : 0.00
% 5.64/2.14  Index Matching       : 0.00
% 5.64/2.14  BG Taut test         : 0.00
%------------------------------------------------------------------------------
