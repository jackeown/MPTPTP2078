%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:50 EST 2020

% Result     : Theorem 2.97s
% Output     : CNFRefutation 3.14s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 103 expanded)
%              Number of leaves         :   39 (  55 expanded)
%              Depth                    :   12
%              Number of atoms          :  134 ( 246 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_waybel_0 > r1_waybel_0 > r1_orders_2 > r2_hidden > r1_tarski > m1_subset_1 > l1_waybel_0 > v7_waybel_0 > v4_orders_2 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > k2_waybel_0 > k6_subset_1 > k4_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_4 > #skF_7 > #skF_6 > #skF_5 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(r2_waybel_0,type,(
    r2_waybel_0: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(r1_orders_2,type,(
    r1_orders_2: ( $i * $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_waybel_0,type,(
    k2_waybel_0: ( $i * $i * $i ) > $i )).

tff(v7_waybel_0,type,(
    v7_waybel_0: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r1_waybel_0,type,(
    r1_waybel_0: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k6_subset_1,type,(
    k6_subset_1: ( $i * $i ) > $i )).

tff(v4_orders_2,type,(
    v4_orders_2: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(l1_waybel_0,type,(
    l1_waybel_0: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_140,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & l1_struct_0(A) )
       => ! [B] :
            ( ( ~ v2_struct_0(B)
              & v4_orders_2(B)
              & v7_waybel_0(B)
              & l1_waybel_0(B,A) )
           => r1_waybel_0(A,B,u1_struct_0(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_yellow_6)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_46,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_34,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_44,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_100,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & l1_waybel_0(B,A) )
         => ! [C] :
              ( r2_waybel_0(A,B,C)
            <=> ~ r1_waybel_0(A,B,k6_subset_1(u1_struct_0(A),C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_waybel_0)).

tff(f_122,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & l1_waybel_0(B,A) )
         => ! [C,D] :
              ( r1_tarski(C,D)
             => ( ( r1_waybel_0(A,B,C)
                 => r1_waybel_0(A,B,D) )
                & ( r2_waybel_0(A,B,C)
                 => r2_waybel_0(A,B,D) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_waybel_0)).

tff(f_37,axiom,(
    ! [A] :
    ? [B] : m1_subset_1(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_subset_1)).

tff(f_83,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & l1_waybel_0(B,A) )
         => ! [C] :
              ( r2_waybel_0(A,B,C)
            <=> ! [D] :
                  ( m1_subset_1(D,u1_struct_0(B))
                 => ? [E] :
                      ( m1_subset_1(E,u1_struct_0(B))
                      & r1_orders_2(B,D,E)
                      & r2_hidden(k2_waybel_0(A,B,E),C) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_waybel_0)).

tff(f_42,axiom,(
    ! [A] :
    ? [B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
      & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc2_subset_1)).

tff(c_54,plain,(
    ~ v2_struct_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_50,plain,(
    ~ v2_struct_0('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_52,plain,(
    l1_struct_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_44,plain,(
    l1_waybel_0('#skF_7','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_18,plain,(
    ! [A_13] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_13)) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_86,plain,(
    ! [C_103,B_104,A_105] :
      ( ~ v1_xboole_0(C_103)
      | ~ m1_subset_1(B_104,k1_zfmisc_1(C_103))
      | ~ r2_hidden(A_105,B_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_95,plain,(
    ! [A_13,A_105] :
      ( ~ v1_xboole_0(A_13)
      | ~ r2_hidden(A_105,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_18,c_86])).

tff(c_99,plain,(
    ! [A_107] : ~ r2_hidden(A_107,k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_95])).

tff(c_104,plain,(
    ! [B_2] : r1_tarski(k1_xboole_0,B_2) ),
    inference(resolution,[status(thm)],[c_6,c_99])).

tff(c_8,plain,(
    ! [A_6] : k4_xboole_0(A_6,k1_xboole_0) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_16,plain,(
    ! [A_11,B_12] : k6_subset_1(A_11,B_12) = k4_xboole_0(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_36,plain,(
    ! [A_73,B_77,C_79] :
      ( r2_waybel_0(A_73,B_77,C_79)
      | r1_waybel_0(A_73,B_77,k6_subset_1(u1_struct_0(A_73),C_79))
      | ~ l1_waybel_0(B_77,A_73)
      | v2_struct_0(B_77)
      | ~ l1_struct_0(A_73)
      | v2_struct_0(A_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_387,plain,(
    ! [A_178,B_179,C_180] :
      ( r2_waybel_0(A_178,B_179,C_180)
      | r1_waybel_0(A_178,B_179,k4_xboole_0(u1_struct_0(A_178),C_180))
      | ~ l1_waybel_0(B_179,A_178)
      | v2_struct_0(B_179)
      | ~ l1_struct_0(A_178)
      | v2_struct_0(A_178) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_36])).

tff(c_432,plain,(
    ! [A_188,B_189] :
      ( r2_waybel_0(A_188,B_189,k1_xboole_0)
      | r1_waybel_0(A_188,B_189,u1_struct_0(A_188))
      | ~ l1_waybel_0(B_189,A_188)
      | v2_struct_0(B_189)
      | ~ l1_struct_0(A_188)
      | v2_struct_0(A_188) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_387])).

tff(c_42,plain,(
    ~ r1_waybel_0('#skF_6','#skF_7',u1_struct_0('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_437,plain,
    ( r2_waybel_0('#skF_6','#skF_7',k1_xboole_0)
    | ~ l1_waybel_0('#skF_7','#skF_6')
    | v2_struct_0('#skF_7')
    | ~ l1_struct_0('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_432,c_42])).

tff(c_441,plain,
    ( r2_waybel_0('#skF_6','#skF_7',k1_xboole_0)
    | v2_struct_0('#skF_7')
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_44,c_437])).

tff(c_442,plain,(
    r2_waybel_0('#skF_6','#skF_7',k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_50,c_441])).

tff(c_38,plain,(
    ! [A_80,B_86,D_90,C_89] :
      ( r2_waybel_0(A_80,B_86,D_90)
      | ~ r2_waybel_0(A_80,B_86,C_89)
      | ~ r1_tarski(C_89,D_90)
      | ~ l1_waybel_0(B_86,A_80)
      | v2_struct_0(B_86)
      | ~ l1_struct_0(A_80)
      | v2_struct_0(A_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_444,plain,(
    ! [D_90] :
      ( r2_waybel_0('#skF_6','#skF_7',D_90)
      | ~ r1_tarski(k1_xboole_0,D_90)
      | ~ l1_waybel_0('#skF_7','#skF_6')
      | v2_struct_0('#skF_7')
      | ~ l1_struct_0('#skF_6')
      | v2_struct_0('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_442,c_38])).

tff(c_447,plain,(
    ! [D_90] :
      ( r2_waybel_0('#skF_6','#skF_7',D_90)
      | v2_struct_0('#skF_7')
      | v2_struct_0('#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_44,c_104,c_444])).

tff(c_448,plain,(
    ! [D_90] : r2_waybel_0('#skF_6','#skF_7',D_90) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_50,c_447])).

tff(c_10,plain,(
    ! [A_7] : m1_subset_1('#skF_2'(A_7),A_7) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_582,plain,(
    ! [A_229,B_230,C_231,D_232] :
      ( r2_hidden(k2_waybel_0(A_229,B_230,'#skF_5'(A_229,B_230,C_231,D_232)),C_231)
      | ~ m1_subset_1(D_232,u1_struct_0(B_230))
      | ~ r2_waybel_0(A_229,B_230,C_231)
      | ~ l1_waybel_0(B_230,A_229)
      | v2_struct_0(B_230)
      | ~ l1_struct_0(A_229)
      | v2_struct_0(A_229) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_98,plain,(
    ! [A_105] : ~ r2_hidden(A_105,k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_95])).

tff(c_631,plain,(
    ! [D_233,B_234,A_235] :
      ( ~ m1_subset_1(D_233,u1_struct_0(B_234))
      | ~ r2_waybel_0(A_235,B_234,k1_xboole_0)
      | ~ l1_waybel_0(B_234,A_235)
      | v2_struct_0(B_234)
      | ~ l1_struct_0(A_235)
      | v2_struct_0(A_235) ) ),
    inference(resolution,[status(thm)],[c_582,c_98])).

tff(c_657,plain,(
    ! [A_236,B_237] :
      ( ~ r2_waybel_0(A_236,B_237,k1_xboole_0)
      | ~ l1_waybel_0(B_237,A_236)
      | v2_struct_0(B_237)
      | ~ l1_struct_0(A_236)
      | v2_struct_0(A_236) ) ),
    inference(resolution,[status(thm)],[c_10,c_631])).

tff(c_661,plain,
    ( ~ l1_waybel_0('#skF_7','#skF_6')
    | v2_struct_0('#skF_7')
    | ~ l1_struct_0('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_448,c_657])).

tff(c_664,plain,
    ( v2_struct_0('#skF_7')
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_44,c_661])).

tff(c_666,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_50,c_664])).

tff(c_667,plain,(
    ! [A_13] : ~ v1_xboole_0(A_13) ),
    inference(splitRight,[status(thm)],[c_95])).

tff(c_12,plain,(
    ! [A_9] : v1_xboole_0('#skF_3'(A_9)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_669,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_667,c_12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n002.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 09:19:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.97/1.55  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.97/1.55  
% 2.97/1.55  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.97/1.56  %$ r2_waybel_0 > r1_waybel_0 > r1_orders_2 > r2_hidden > r1_tarski > m1_subset_1 > l1_waybel_0 > v7_waybel_0 > v4_orders_2 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > k2_waybel_0 > k6_subset_1 > k4_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_4 > #skF_7 > #skF_6 > #skF_5 > #skF_3 > #skF_1
% 2.97/1.56  
% 2.97/1.56  %Foreground sorts:
% 2.97/1.56  
% 2.97/1.56  
% 2.97/1.56  %Background operators:
% 2.97/1.56  
% 2.97/1.56  
% 2.97/1.56  %Foreground operators:
% 2.97/1.56  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.97/1.56  tff(r2_waybel_0, type, r2_waybel_0: ($i * $i * $i) > $o).
% 2.97/1.56  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.97/1.56  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.97/1.56  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.97/1.56  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.97/1.56  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 2.97/1.56  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.97/1.56  tff(k2_waybel_0, type, k2_waybel_0: ($i * $i * $i) > $i).
% 2.97/1.56  tff(v7_waybel_0, type, v7_waybel_0: $i > $o).
% 2.97/1.56  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.97/1.56  tff('#skF_7', type, '#skF_7': $i).
% 2.97/1.56  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.97/1.56  tff(r1_waybel_0, type, r1_waybel_0: ($i * $i * $i) > $o).
% 2.97/1.56  tff('#skF_6', type, '#skF_6': $i).
% 2.97/1.56  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 2.97/1.56  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 2.97/1.56  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.97/1.56  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.97/1.56  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.97/1.56  tff(l1_waybel_0, type, l1_waybel_0: ($i * $i) > $o).
% 2.97/1.56  tff('#skF_5', type, '#skF_5': ($i * $i * $i * $i) > $i).
% 2.97/1.56  tff('#skF_3', type, '#skF_3': $i > $i).
% 2.97/1.56  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.97/1.56  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.97/1.56  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.97/1.56  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.97/1.56  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.97/1.56  
% 3.14/1.57  tff(f_140, negated_conjecture, ~(![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: ((((~v2_struct_0(B) & v4_orders_2(B)) & v7_waybel_0(B)) & l1_waybel_0(B, A)) => r1_waybel_0(A, B, u1_struct_0(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_yellow_6)).
% 3.14/1.57  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 3.14/1.57  tff(f_46, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 3.14/1.57  tff(f_59, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 3.14/1.57  tff(f_34, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 3.14/1.57  tff(f_44, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 3.14/1.57  tff(f_100, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: ((~v2_struct_0(B) & l1_waybel_0(B, A)) => (![C]: (r2_waybel_0(A, B, C) <=> ~r1_waybel_0(A, B, k6_subset_1(u1_struct_0(A), C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_waybel_0)).
% 3.14/1.57  tff(f_122, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: ((~v2_struct_0(B) & l1_waybel_0(B, A)) => (![C, D]: (r1_tarski(C, D) => ((r1_waybel_0(A, B, C) => r1_waybel_0(A, B, D)) & (r2_waybel_0(A, B, C) => r2_waybel_0(A, B, D))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_waybel_0)).
% 3.14/1.57  tff(f_37, axiom, (![A]: (?[B]: m1_subset_1(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', existence_m1_subset_1)).
% 3.14/1.57  tff(f_83, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: ((~v2_struct_0(B) & l1_waybel_0(B, A)) => (![C]: (r2_waybel_0(A, B, C) <=> (![D]: (m1_subset_1(D, u1_struct_0(B)) => (?[E]: ((m1_subset_1(E, u1_struct_0(B)) & r1_orders_2(B, D, E)) & r2_hidden(k2_waybel_0(A, B, E), C))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d12_waybel_0)).
% 3.14/1.57  tff(f_42, axiom, (![A]: (?[B]: (m1_subset_1(B, k1_zfmisc_1(A)) & v1_xboole_0(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc2_subset_1)).
% 3.14/1.57  tff(c_54, plain, (~v2_struct_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_140])).
% 3.14/1.57  tff(c_50, plain, (~v2_struct_0('#skF_7')), inference(cnfTransformation, [status(thm)], [f_140])).
% 3.14/1.57  tff(c_52, plain, (l1_struct_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_140])).
% 3.14/1.57  tff(c_44, plain, (l1_waybel_0('#skF_7', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_140])).
% 3.14/1.57  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.14/1.57  tff(c_18, plain, (![A_13]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_13)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.14/1.57  tff(c_86, plain, (![C_103, B_104, A_105]: (~v1_xboole_0(C_103) | ~m1_subset_1(B_104, k1_zfmisc_1(C_103)) | ~r2_hidden(A_105, B_104))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.14/1.57  tff(c_95, plain, (![A_13, A_105]: (~v1_xboole_0(A_13) | ~r2_hidden(A_105, k1_xboole_0))), inference(resolution, [status(thm)], [c_18, c_86])).
% 3.14/1.57  tff(c_99, plain, (![A_107]: (~r2_hidden(A_107, k1_xboole_0))), inference(splitLeft, [status(thm)], [c_95])).
% 3.14/1.57  tff(c_104, plain, (![B_2]: (r1_tarski(k1_xboole_0, B_2))), inference(resolution, [status(thm)], [c_6, c_99])).
% 3.14/1.57  tff(c_8, plain, (![A_6]: (k4_xboole_0(A_6, k1_xboole_0)=A_6)), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.14/1.57  tff(c_16, plain, (![A_11, B_12]: (k6_subset_1(A_11, B_12)=k4_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.14/1.57  tff(c_36, plain, (![A_73, B_77, C_79]: (r2_waybel_0(A_73, B_77, C_79) | r1_waybel_0(A_73, B_77, k6_subset_1(u1_struct_0(A_73), C_79)) | ~l1_waybel_0(B_77, A_73) | v2_struct_0(B_77) | ~l1_struct_0(A_73) | v2_struct_0(A_73))), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.14/1.57  tff(c_387, plain, (![A_178, B_179, C_180]: (r2_waybel_0(A_178, B_179, C_180) | r1_waybel_0(A_178, B_179, k4_xboole_0(u1_struct_0(A_178), C_180)) | ~l1_waybel_0(B_179, A_178) | v2_struct_0(B_179) | ~l1_struct_0(A_178) | v2_struct_0(A_178))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_36])).
% 3.14/1.57  tff(c_432, plain, (![A_188, B_189]: (r2_waybel_0(A_188, B_189, k1_xboole_0) | r1_waybel_0(A_188, B_189, u1_struct_0(A_188)) | ~l1_waybel_0(B_189, A_188) | v2_struct_0(B_189) | ~l1_struct_0(A_188) | v2_struct_0(A_188))), inference(superposition, [status(thm), theory('equality')], [c_8, c_387])).
% 3.14/1.57  tff(c_42, plain, (~r1_waybel_0('#skF_6', '#skF_7', u1_struct_0('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_140])).
% 3.14/1.57  tff(c_437, plain, (r2_waybel_0('#skF_6', '#skF_7', k1_xboole_0) | ~l1_waybel_0('#skF_7', '#skF_6') | v2_struct_0('#skF_7') | ~l1_struct_0('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_432, c_42])).
% 3.14/1.57  tff(c_441, plain, (r2_waybel_0('#skF_6', '#skF_7', k1_xboole_0) | v2_struct_0('#skF_7') | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_44, c_437])).
% 3.14/1.57  tff(c_442, plain, (r2_waybel_0('#skF_6', '#skF_7', k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_54, c_50, c_441])).
% 3.14/1.57  tff(c_38, plain, (![A_80, B_86, D_90, C_89]: (r2_waybel_0(A_80, B_86, D_90) | ~r2_waybel_0(A_80, B_86, C_89) | ~r1_tarski(C_89, D_90) | ~l1_waybel_0(B_86, A_80) | v2_struct_0(B_86) | ~l1_struct_0(A_80) | v2_struct_0(A_80))), inference(cnfTransformation, [status(thm)], [f_122])).
% 3.14/1.57  tff(c_444, plain, (![D_90]: (r2_waybel_0('#skF_6', '#skF_7', D_90) | ~r1_tarski(k1_xboole_0, D_90) | ~l1_waybel_0('#skF_7', '#skF_6') | v2_struct_0('#skF_7') | ~l1_struct_0('#skF_6') | v2_struct_0('#skF_6'))), inference(resolution, [status(thm)], [c_442, c_38])).
% 3.14/1.57  tff(c_447, plain, (![D_90]: (r2_waybel_0('#skF_6', '#skF_7', D_90) | v2_struct_0('#skF_7') | v2_struct_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_44, c_104, c_444])).
% 3.14/1.57  tff(c_448, plain, (![D_90]: (r2_waybel_0('#skF_6', '#skF_7', D_90))), inference(negUnitSimplification, [status(thm)], [c_54, c_50, c_447])).
% 3.14/1.57  tff(c_10, plain, (![A_7]: (m1_subset_1('#skF_2'(A_7), A_7))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.14/1.57  tff(c_582, plain, (![A_229, B_230, C_231, D_232]: (r2_hidden(k2_waybel_0(A_229, B_230, '#skF_5'(A_229, B_230, C_231, D_232)), C_231) | ~m1_subset_1(D_232, u1_struct_0(B_230)) | ~r2_waybel_0(A_229, B_230, C_231) | ~l1_waybel_0(B_230, A_229) | v2_struct_0(B_230) | ~l1_struct_0(A_229) | v2_struct_0(A_229))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.14/1.57  tff(c_98, plain, (![A_105]: (~r2_hidden(A_105, k1_xboole_0))), inference(splitLeft, [status(thm)], [c_95])).
% 3.14/1.57  tff(c_631, plain, (![D_233, B_234, A_235]: (~m1_subset_1(D_233, u1_struct_0(B_234)) | ~r2_waybel_0(A_235, B_234, k1_xboole_0) | ~l1_waybel_0(B_234, A_235) | v2_struct_0(B_234) | ~l1_struct_0(A_235) | v2_struct_0(A_235))), inference(resolution, [status(thm)], [c_582, c_98])).
% 3.14/1.57  tff(c_657, plain, (![A_236, B_237]: (~r2_waybel_0(A_236, B_237, k1_xboole_0) | ~l1_waybel_0(B_237, A_236) | v2_struct_0(B_237) | ~l1_struct_0(A_236) | v2_struct_0(A_236))), inference(resolution, [status(thm)], [c_10, c_631])).
% 3.14/1.57  tff(c_661, plain, (~l1_waybel_0('#skF_7', '#skF_6') | v2_struct_0('#skF_7') | ~l1_struct_0('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_448, c_657])).
% 3.14/1.57  tff(c_664, plain, (v2_struct_0('#skF_7') | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_44, c_661])).
% 3.14/1.57  tff(c_666, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_50, c_664])).
% 3.14/1.57  tff(c_667, plain, (![A_13]: (~v1_xboole_0(A_13))), inference(splitRight, [status(thm)], [c_95])).
% 3.14/1.57  tff(c_12, plain, (![A_9]: (v1_xboole_0('#skF_3'(A_9)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.14/1.57  tff(c_669, plain, $false, inference(negUnitSimplification, [status(thm)], [c_667, c_12])).
% 3.14/1.57  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.14/1.57  
% 3.14/1.57  Inference rules
% 3.14/1.57  ----------------------
% 3.14/1.57  #Ref     : 0
% 3.14/1.57  #Sup     : 130
% 3.14/1.57  #Fact    : 0
% 3.14/1.57  #Define  : 0
% 3.14/1.57  #Split   : 1
% 3.14/1.57  #Chain   : 0
% 3.14/1.57  #Close   : 0
% 3.14/1.57  
% 3.14/1.57  Ordering : KBO
% 3.14/1.57  
% 3.14/1.57  Simplification rules
% 3.14/1.57  ----------------------
% 3.14/1.57  #Subsume      : 57
% 3.14/1.57  #Demod        : 23
% 3.14/1.57  #Tautology    : 19
% 3.14/1.57  #SimpNegUnit  : 5
% 3.14/1.57  #BackRed      : 1
% 3.14/1.57  
% 3.14/1.57  #Partial instantiations: 0
% 3.14/1.57  #Strategies tried      : 1
% 3.14/1.57  
% 3.14/1.57  Timing (in seconds)
% 3.14/1.57  ----------------------
% 3.14/1.57  Preprocessing        : 0.44
% 3.14/1.58  Parsing              : 0.24
% 3.14/1.58  CNF conversion       : 0.04
% 3.14/1.58  Main loop            : 0.36
% 3.14/1.58  Inferencing          : 0.14
% 3.14/1.58  Reduction            : 0.10
% 3.14/1.58  Demodulation         : 0.07
% 3.14/1.58  BG Simplification    : 0.02
% 3.14/1.58  Subsumption          : 0.07
% 3.14/1.58  Abstraction          : 0.02
% 3.14/1.58  MUC search           : 0.00
% 3.14/1.58  Cooper               : 0.00
% 3.14/1.58  Total                : 0.83
% 3.14/1.58  Index Insertion      : 0.00
% 3.14/1.58  Index Deletion       : 0.00
% 3.14/1.58  Index Matching       : 0.00
% 3.14/1.58  BG Taut test         : 0.00
%------------------------------------------------------------------------------
