%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:25:23 EST 2020

% Result     : Theorem 4.57s
% Output     : CNFRefutation 4.89s
% Verified   : 
% Statistics : Number of formulae       :  175 (1031 expanded)
%              Number of leaves         :   42 ( 419 expanded)
%              Depth                    :   20
%              Number of atoms          :  707 (3381 expanded)
%              Number of equality atoms :   70 ( 636 expanded)
%              Maximal formula depth    :   17 (   7 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r3_orders_2 > r1_orders_2 > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v2_lattice3 > v1_xboole_0 > v1_orders_2 > l1_orders_2 > k2_enumset1 > k12_lattice3 > k11_lattice3 > k3_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > u1_orders_2 > k2_yellow_1 > k1_yellow_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_orders_2,type,(
    v1_orders_2: $i > $o )).

tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(r3_orders_2,type,(
    r3_orders_2: ( $i * $i * $i ) > $o )).

tff(v3_orders_2,type,(
    v3_orders_2: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_orders_2,type,(
    r1_orders_2: ( $i * $i * $i ) > $o )).

tff(k2_yellow_1,type,(
    k2_yellow_1: $i > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k11_lattice3,type,(
    k11_lattice3: ( $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k12_lattice3,type,(
    k12_lattice3: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v4_orders_2,type,(
    v4_orders_2: $i > $o )).

tff(v5_orders_2,type,(
    v5_orders_2: $i > $o )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k1_yellow_1,type,(
    k1_yellow_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(v2_lattice3,type,(
    v2_lattice3: $i > $o )).

tff(u1_orders_2,type,(
    u1_orders_2: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_149,axiom,(
    ! [A] :
      ( u1_struct_0(k2_yellow_1(A)) = A
      & u1_orders_2(k2_yellow_1(A)) = k1_yellow_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_yellow_1)).

tff(f_176,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ( v2_lattice3(k2_yellow_1(A))
         => ! [B] :
              ( m1_subset_1(B,u1_struct_0(k2_yellow_1(A)))
             => ! [C] :
                  ( m1_subset_1(C,u1_struct_0(k2_yellow_1(A)))
                 => r1_tarski(k11_lattice3(k2_yellow_1(A),B,C),k3_xboole_0(B,C)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_yellow_1)).

tff(f_137,axiom,(
    ! [A] :
      ( v1_orders_2(k2_yellow_1(A))
      & l1_orders_2(k2_yellow_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_yellow_1)).

tff(f_56,axiom,(
    ! [A,B,C] :
      ( ( l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => m1_subset_1(k11_lattice3(A,B,C),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k11_lattice3)).

tff(f_145,axiom,(
    ! [A] :
      ( v1_orders_2(k2_yellow_1(A))
      & v3_orders_2(k2_yellow_1(A))
      & v4_orders_2(k2_yellow_1(A))
      & v5_orders_2(k2_yellow_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_yellow_1)).

tff(f_162,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(k2_yellow_1(A)))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(k2_yellow_1(A)))
             => ( r3_orders_2(k2_yellow_1(A),B,C)
              <=> r1_tarski(B,C) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_yellow_1)).

tff(f_133,axiom,(
    ! [A] :
      ( ( v3_orders_2(A)
        & v5_orders_2(A)
        & v2_lattice3(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( B = k12_lattice3(A,B,C)
              <=> r3_orders_2(A,B,C) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_yellow_0)).

tff(f_101,axiom,(
    ! [A,B,C] :
      ( ( v5_orders_2(A)
        & v2_lattice3(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => k12_lattice3(A,B,C) = k11_lattice3(A,B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k12_lattice3)).

tff(f_89,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v5_orders_2(A)
        & v2_lattice3(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ! [D] :
                  ( m1_subset_1(D,u1_struct_0(A))
                 => ( D = k11_lattice3(A,B,C)
                  <=> ( r1_orders_2(A,D,B)
                      & r1_orders_2(A,D,C)
                      & ! [E] :
                          ( m1_subset_1(E,u1_struct_0(A))
                         => ( ( r1_orders_2(A,E,B)
                              & r1_orders_2(A,E,C) )
                           => r1_orders_2(A,E,D) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l28_lattice3)).

tff(f_48,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ( v2_lattice3(A)
       => ~ v2_struct_0(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_lattice3)).

tff(f_115,axiom,(
    ! [A] :
      ( ( v5_orders_2(A)
        & v2_lattice3(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => k11_lattice3(A,B,C) = k11_lattice3(A,C,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_lattice3)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C) )
     => r1_tarski(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).

tff(c_52,plain,(
    ! [A_79] : u1_struct_0(k2_yellow_1(A_79)) = A_79 ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_62,plain,(
    m1_subset_1('#skF_4',u1_struct_0(k2_yellow_1('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_70,plain,(
    m1_subset_1('#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_62])).

tff(c_64,plain,(
    m1_subset_1('#skF_3',u1_struct_0(k2_yellow_1('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_69,plain,(
    m1_subset_1('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_64])).

tff(c_42,plain,(
    ! [A_77] : l1_orders_2(k2_yellow_1(A_77)) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_1402,plain,(
    ! [A_252,B_253,C_254] :
      ( m1_subset_1(k11_lattice3(A_252,B_253,C_254),u1_struct_0(A_252))
      | ~ m1_subset_1(C_254,u1_struct_0(A_252))
      | ~ m1_subset_1(B_253,u1_struct_0(A_252))
      | ~ l1_orders_2(A_252) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_1405,plain,(
    ! [A_79,B_253,C_254] :
      ( m1_subset_1(k11_lattice3(k2_yellow_1(A_79),B_253,C_254),A_79)
      | ~ m1_subset_1(C_254,u1_struct_0(k2_yellow_1(A_79)))
      | ~ m1_subset_1(B_253,u1_struct_0(k2_yellow_1(A_79)))
      | ~ l1_orders_2(k2_yellow_1(A_79)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_1402])).

tff(c_1407,plain,(
    ! [A_79,B_253,C_254] :
      ( m1_subset_1(k11_lattice3(k2_yellow_1(A_79),B_253,C_254),A_79)
      | ~ m1_subset_1(C_254,A_79)
      | ~ m1_subset_1(B_253,A_79) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_52,c_52,c_1405])).

tff(c_66,plain,(
    v2_lattice3(k2_yellow_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_50,plain,(
    ! [A_78] : v5_orders_2(k2_yellow_1(A_78)) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_68,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_46,plain,(
    ! [A_78] : v3_orders_2(k2_yellow_1(A_78)) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_56,plain,(
    ! [A_80,B_84,C_86] :
      ( r3_orders_2(k2_yellow_1(A_80),B_84,C_86)
      | ~ r1_tarski(B_84,C_86)
      | ~ m1_subset_1(C_86,u1_struct_0(k2_yellow_1(A_80)))
      | ~ m1_subset_1(B_84,u1_struct_0(k2_yellow_1(A_80)))
      | v1_xboole_0(A_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_72,plain,(
    ! [A_80,B_84,C_86] :
      ( r3_orders_2(k2_yellow_1(A_80),B_84,C_86)
      | ~ r1_tarski(B_84,C_86)
      | ~ m1_subset_1(C_86,A_80)
      | ~ m1_subset_1(B_84,A_80)
      | v1_xboole_0(A_80) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_52,c_56])).

tff(c_1586,plain,(
    ! [A_287,B_288,C_289] :
      ( k12_lattice3(A_287,B_288,C_289) = B_288
      | ~ r3_orders_2(A_287,B_288,C_289)
      | ~ m1_subset_1(C_289,u1_struct_0(A_287))
      | ~ m1_subset_1(B_288,u1_struct_0(A_287))
      | ~ l1_orders_2(A_287)
      | ~ v2_lattice3(A_287)
      | ~ v5_orders_2(A_287)
      | ~ v3_orders_2(A_287) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_1590,plain,(
    ! [A_80,B_84,C_86] :
      ( k12_lattice3(k2_yellow_1(A_80),B_84,C_86) = B_84
      | ~ m1_subset_1(C_86,u1_struct_0(k2_yellow_1(A_80)))
      | ~ m1_subset_1(B_84,u1_struct_0(k2_yellow_1(A_80)))
      | ~ l1_orders_2(k2_yellow_1(A_80))
      | ~ v2_lattice3(k2_yellow_1(A_80))
      | ~ v5_orders_2(k2_yellow_1(A_80))
      | ~ v3_orders_2(k2_yellow_1(A_80))
      | ~ r1_tarski(B_84,C_86)
      | ~ m1_subset_1(C_86,A_80)
      | ~ m1_subset_1(B_84,A_80)
      | v1_xboole_0(A_80) ) ),
    inference(resolution,[status(thm)],[c_72,c_1586])).

tff(c_1597,plain,(
    ! [A_290,B_291,C_292] :
      ( k12_lattice3(k2_yellow_1(A_290),B_291,C_292) = B_291
      | ~ v2_lattice3(k2_yellow_1(A_290))
      | ~ r1_tarski(B_291,C_292)
      | ~ m1_subset_1(C_292,A_290)
      | ~ m1_subset_1(B_291,A_290)
      | v1_xboole_0(A_290) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_50,c_42,c_52,c_52,c_1590])).

tff(c_1599,plain,(
    ! [B_291,C_292] :
      ( k12_lattice3(k2_yellow_1('#skF_2'),B_291,C_292) = B_291
      | ~ r1_tarski(B_291,C_292)
      | ~ m1_subset_1(C_292,'#skF_2')
      | ~ m1_subset_1(B_291,'#skF_2')
      | v1_xboole_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_66,c_1597])).

tff(c_1603,plain,(
    ! [B_293,C_294] :
      ( k12_lattice3(k2_yellow_1('#skF_2'),B_293,C_294) = B_293
      | ~ r1_tarski(B_293,C_294)
      | ~ m1_subset_1(C_294,'#skF_2')
      | ~ m1_subset_1(B_293,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_1599])).

tff(c_1518,plain,(
    ! [A_266,B_267,C_268] :
      ( k12_lattice3(A_266,B_267,C_268) = k11_lattice3(A_266,B_267,C_268)
      | ~ m1_subset_1(C_268,u1_struct_0(A_266))
      | ~ m1_subset_1(B_267,u1_struct_0(A_266))
      | ~ l1_orders_2(A_266)
      | ~ v2_lattice3(A_266)
      | ~ v5_orders_2(A_266) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_1525,plain,(
    ! [A_79,B_267,C_268] :
      ( k12_lattice3(k2_yellow_1(A_79),B_267,C_268) = k11_lattice3(k2_yellow_1(A_79),B_267,C_268)
      | ~ m1_subset_1(C_268,A_79)
      | ~ m1_subset_1(B_267,u1_struct_0(k2_yellow_1(A_79)))
      | ~ l1_orders_2(k2_yellow_1(A_79))
      | ~ v2_lattice3(k2_yellow_1(A_79))
      | ~ v5_orders_2(k2_yellow_1(A_79)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_1518])).

tff(c_1536,plain,(
    ! [A_269,B_270,C_271] :
      ( k12_lattice3(k2_yellow_1(A_269),B_270,C_271) = k11_lattice3(k2_yellow_1(A_269),B_270,C_271)
      | ~ m1_subset_1(C_271,A_269)
      | ~ m1_subset_1(B_270,A_269)
      | ~ v2_lattice3(k2_yellow_1(A_269)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_42,c_52,c_1525])).

tff(c_1539,plain,(
    ! [B_270,C_271] :
      ( k12_lattice3(k2_yellow_1('#skF_2'),B_270,C_271) = k11_lattice3(k2_yellow_1('#skF_2'),B_270,C_271)
      | ~ m1_subset_1(C_271,'#skF_2')
      | ~ m1_subset_1(B_270,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_66,c_1536])).

tff(c_1611,plain,(
    ! [B_293,C_294] :
      ( k11_lattice3(k2_yellow_1('#skF_2'),B_293,C_294) = B_293
      | ~ m1_subset_1(C_294,'#skF_2')
      | ~ m1_subset_1(B_293,'#skF_2')
      | ~ r1_tarski(B_293,C_294)
      | ~ m1_subset_1(C_294,'#skF_2')
      | ~ m1_subset_1(B_293,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1603,c_1539])).

tff(c_1703,plain,(
    ! [A_297,B_298,C_299] :
      ( r1_orders_2(A_297,k11_lattice3(A_297,B_298,C_299),B_298)
      | ~ m1_subset_1(k11_lattice3(A_297,B_298,C_299),u1_struct_0(A_297))
      | ~ m1_subset_1(C_299,u1_struct_0(A_297))
      | ~ m1_subset_1(B_298,u1_struct_0(A_297))
      | ~ l1_orders_2(A_297)
      | ~ v2_lattice3(A_297)
      | ~ v5_orders_2(A_297)
      | v2_struct_0(A_297) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_1705,plain,(
    ! [B_293,C_294] :
      ( r1_orders_2(k2_yellow_1('#skF_2'),k11_lattice3(k2_yellow_1('#skF_2'),B_293,C_294),B_293)
      | ~ m1_subset_1(B_293,u1_struct_0(k2_yellow_1('#skF_2')))
      | ~ m1_subset_1(C_294,u1_struct_0(k2_yellow_1('#skF_2')))
      | ~ m1_subset_1(B_293,u1_struct_0(k2_yellow_1('#skF_2')))
      | ~ l1_orders_2(k2_yellow_1('#skF_2'))
      | ~ v2_lattice3(k2_yellow_1('#skF_2'))
      | ~ v5_orders_2(k2_yellow_1('#skF_2'))
      | v2_struct_0(k2_yellow_1('#skF_2'))
      | ~ m1_subset_1(C_294,'#skF_2')
      | ~ m1_subset_1(B_293,'#skF_2')
      | ~ r1_tarski(B_293,C_294)
      | ~ m1_subset_1(C_294,'#skF_2')
      | ~ m1_subset_1(B_293,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1611,c_1703])).

tff(c_1715,plain,(
    ! [B_293,C_294] :
      ( r1_orders_2(k2_yellow_1('#skF_2'),k11_lattice3(k2_yellow_1('#skF_2'),B_293,C_294),B_293)
      | v2_struct_0(k2_yellow_1('#skF_2'))
      | ~ r1_tarski(B_293,C_294)
      | ~ m1_subset_1(C_294,'#skF_2')
      | ~ m1_subset_1(B_293,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_66,c_42,c_52,c_52,c_52,c_1705])).

tff(c_1723,plain,(
    v2_struct_0(k2_yellow_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_1715])).

tff(c_14,plain,(
    ! [A_10] :
      ( ~ v2_struct_0(A_10)
      | ~ v2_lattice3(A_10)
      | ~ l1_orders_2(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_1726,plain,
    ( ~ v2_lattice3(k2_yellow_1('#skF_2'))
    | ~ l1_orders_2(k2_yellow_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_1723,c_14])).

tff(c_1730,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_66,c_1726])).

tff(c_1732,plain,(
    ~ v2_struct_0(k2_yellow_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_1715])).

tff(c_1408,plain,(
    ! [A_255,C_256,B_257] :
      ( k11_lattice3(A_255,C_256,B_257) = k11_lattice3(A_255,B_257,C_256)
      | ~ m1_subset_1(C_256,u1_struct_0(A_255))
      | ~ m1_subset_1(B_257,u1_struct_0(A_255))
      | ~ l1_orders_2(A_255)
      | ~ v2_lattice3(A_255)
      | ~ v5_orders_2(A_255) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_1412,plain,(
    ! [A_79,C_256,B_257] :
      ( k11_lattice3(k2_yellow_1(A_79),C_256,B_257) = k11_lattice3(k2_yellow_1(A_79),B_257,C_256)
      | ~ m1_subset_1(C_256,A_79)
      | ~ m1_subset_1(B_257,u1_struct_0(k2_yellow_1(A_79)))
      | ~ l1_orders_2(k2_yellow_1(A_79))
      | ~ v2_lattice3(k2_yellow_1(A_79))
      | ~ v5_orders_2(k2_yellow_1(A_79)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_1408])).

tff(c_1421,plain,(
    ! [A_261,C_262,B_263] :
      ( k11_lattice3(k2_yellow_1(A_261),C_262,B_263) = k11_lattice3(k2_yellow_1(A_261),B_263,C_262)
      | ~ m1_subset_1(C_262,A_261)
      | ~ m1_subset_1(B_263,A_261)
      | ~ v2_lattice3(k2_yellow_1(A_261)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_42,c_52,c_1412])).

tff(c_1424,plain,(
    ! [C_262,B_263] :
      ( k11_lattice3(k2_yellow_1('#skF_2'),C_262,B_263) = k11_lattice3(k2_yellow_1('#skF_2'),B_263,C_262)
      | ~ m1_subset_1(C_262,'#skF_2')
      | ~ m1_subset_1(B_263,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_66,c_1421])).

tff(c_16,plain,(
    ! [A_11,B_12,C_13] :
      ( m1_subset_1(k11_lattice3(A_11,B_12,C_13),u1_struct_0(A_11))
      | ~ m1_subset_1(C_13,u1_struct_0(A_11))
      | ~ m1_subset_1(B_12,u1_struct_0(A_11))
      | ~ l1_orders_2(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_1733,plain,(
    ! [A_300,B_301,C_302] :
      ( r1_orders_2(A_300,k11_lattice3(A_300,B_301,C_302),C_302)
      | ~ m1_subset_1(k11_lattice3(A_300,B_301,C_302),u1_struct_0(A_300))
      | ~ m1_subset_1(C_302,u1_struct_0(A_300))
      | ~ m1_subset_1(B_301,u1_struct_0(A_300))
      | ~ l1_orders_2(A_300)
      | ~ v2_lattice3(A_300)
      | ~ v5_orders_2(A_300)
      | v2_struct_0(A_300) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_1842,plain,(
    ! [A_323,B_324,C_325] :
      ( r1_orders_2(A_323,k11_lattice3(A_323,B_324,C_325),C_325)
      | ~ v2_lattice3(A_323)
      | ~ v5_orders_2(A_323)
      | v2_struct_0(A_323)
      | ~ m1_subset_1(C_325,u1_struct_0(A_323))
      | ~ m1_subset_1(B_324,u1_struct_0(A_323))
      | ~ l1_orders_2(A_323) ) ),
    inference(resolution,[status(thm)],[c_16,c_1733])).

tff(c_1848,plain,(
    ! [C_262,B_263] :
      ( r1_orders_2(k2_yellow_1('#skF_2'),k11_lattice3(k2_yellow_1('#skF_2'),C_262,B_263),C_262)
      | ~ v2_lattice3(k2_yellow_1('#skF_2'))
      | ~ v5_orders_2(k2_yellow_1('#skF_2'))
      | v2_struct_0(k2_yellow_1('#skF_2'))
      | ~ m1_subset_1(C_262,u1_struct_0(k2_yellow_1('#skF_2')))
      | ~ m1_subset_1(B_263,u1_struct_0(k2_yellow_1('#skF_2')))
      | ~ l1_orders_2(k2_yellow_1('#skF_2'))
      | ~ m1_subset_1(C_262,'#skF_2')
      | ~ m1_subset_1(B_263,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1424,c_1842])).

tff(c_1856,plain,(
    ! [C_262,B_263] :
      ( r1_orders_2(k2_yellow_1('#skF_2'),k11_lattice3(k2_yellow_1('#skF_2'),C_262,B_263),C_262)
      | v2_struct_0(k2_yellow_1('#skF_2'))
      | ~ m1_subset_1(C_262,'#skF_2')
      | ~ m1_subset_1(B_263,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_52,c_52,c_50,c_66,c_1848])).

tff(c_1857,plain,(
    ! [C_262,B_263] :
      ( r1_orders_2(k2_yellow_1('#skF_2'),k11_lattice3(k2_yellow_1('#skF_2'),C_262,B_263),C_262)
      | ~ m1_subset_1(C_262,'#skF_2')
      | ~ m1_subset_1(B_263,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_1732,c_1856])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1845,plain,(
    ! [B_293,C_294] :
      ( r1_orders_2(k2_yellow_1('#skF_2'),B_293,C_294)
      | ~ v2_lattice3(k2_yellow_1('#skF_2'))
      | ~ v5_orders_2(k2_yellow_1('#skF_2'))
      | v2_struct_0(k2_yellow_1('#skF_2'))
      | ~ m1_subset_1(C_294,u1_struct_0(k2_yellow_1('#skF_2')))
      | ~ m1_subset_1(B_293,u1_struct_0(k2_yellow_1('#skF_2')))
      | ~ l1_orders_2(k2_yellow_1('#skF_2'))
      | ~ m1_subset_1(C_294,'#skF_2')
      | ~ m1_subset_1(B_293,'#skF_2')
      | ~ r1_tarski(B_293,C_294)
      | ~ m1_subset_1(C_294,'#skF_2')
      | ~ m1_subset_1(B_293,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1611,c_1842])).

tff(c_1853,plain,(
    ! [B_293,C_294] :
      ( r1_orders_2(k2_yellow_1('#skF_2'),B_293,C_294)
      | v2_struct_0(k2_yellow_1('#skF_2'))
      | ~ r1_tarski(B_293,C_294)
      | ~ m1_subset_1(C_294,'#skF_2')
      | ~ m1_subset_1(B_293,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_52,c_52,c_50,c_66,c_1845])).

tff(c_1854,plain,(
    ! [B_293,C_294] :
      ( r1_orders_2(k2_yellow_1('#skF_2'),B_293,C_294)
      | ~ r1_tarski(B_293,C_294)
      | ~ m1_subset_1(C_294,'#skF_2')
      | ~ m1_subset_1(B_293,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_1732,c_1853])).

tff(c_20,plain,(
    ! [A_14,B_38,C_50,D_56] :
      ( r1_orders_2(A_14,'#skF_1'(A_14,B_38,C_50,D_56),C_50)
      | k11_lattice3(A_14,B_38,C_50) = D_56
      | ~ r1_orders_2(A_14,D_56,C_50)
      | ~ r1_orders_2(A_14,D_56,B_38)
      | ~ m1_subset_1(D_56,u1_struct_0(A_14))
      | ~ m1_subset_1(C_50,u1_struct_0(A_14))
      | ~ m1_subset_1(B_38,u1_struct_0(A_14))
      | ~ l1_orders_2(A_14)
      | ~ v2_lattice3(A_14)
      | ~ v5_orders_2(A_14)
      | v2_struct_0(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_2060,plain,(
    ! [A_353,B_354,C_355,D_356] :
      ( ~ r1_orders_2(A_353,'#skF_1'(A_353,B_354,C_355,D_356),D_356)
      | k11_lattice3(A_353,B_354,C_355) = D_356
      | ~ r1_orders_2(A_353,D_356,C_355)
      | ~ r1_orders_2(A_353,D_356,B_354)
      | ~ m1_subset_1(D_356,u1_struct_0(A_353))
      | ~ m1_subset_1(C_355,u1_struct_0(A_353))
      | ~ m1_subset_1(B_354,u1_struct_0(A_353))
      | ~ l1_orders_2(A_353)
      | ~ v2_lattice3(A_353)
      | ~ v5_orders_2(A_353)
      | v2_struct_0(A_353) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_2079,plain,(
    ! [A_357,B_358,C_359] :
      ( k11_lattice3(A_357,B_358,C_359) = C_359
      | ~ r1_orders_2(A_357,C_359,C_359)
      | ~ r1_orders_2(A_357,C_359,B_358)
      | ~ m1_subset_1(C_359,u1_struct_0(A_357))
      | ~ m1_subset_1(B_358,u1_struct_0(A_357))
      | ~ l1_orders_2(A_357)
      | ~ v2_lattice3(A_357)
      | ~ v5_orders_2(A_357)
      | v2_struct_0(A_357) ) ),
    inference(resolution,[status(thm)],[c_20,c_2060])).

tff(c_2082,plain,(
    ! [B_358,C_294] :
      ( k11_lattice3(k2_yellow_1('#skF_2'),B_358,C_294) = C_294
      | ~ r1_orders_2(k2_yellow_1('#skF_2'),C_294,B_358)
      | ~ m1_subset_1(C_294,u1_struct_0(k2_yellow_1('#skF_2')))
      | ~ m1_subset_1(B_358,u1_struct_0(k2_yellow_1('#skF_2')))
      | ~ l1_orders_2(k2_yellow_1('#skF_2'))
      | ~ v2_lattice3(k2_yellow_1('#skF_2'))
      | ~ v5_orders_2(k2_yellow_1('#skF_2'))
      | v2_struct_0(k2_yellow_1('#skF_2'))
      | ~ r1_tarski(C_294,C_294)
      | ~ m1_subset_1(C_294,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_1854,c_2079])).

tff(c_2087,plain,(
    ! [B_358,C_294] :
      ( k11_lattice3(k2_yellow_1('#skF_2'),B_358,C_294) = C_294
      | ~ r1_orders_2(k2_yellow_1('#skF_2'),C_294,B_358)
      | ~ m1_subset_1(B_358,'#skF_2')
      | v2_struct_0(k2_yellow_1('#skF_2'))
      | ~ m1_subset_1(C_294,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_50,c_66,c_42,c_52,c_52,c_2082])).

tff(c_2093,plain,(
    ! [B_360,C_361] :
      ( k11_lattice3(k2_yellow_1('#skF_2'),B_360,C_361) = C_361
      | ~ r1_orders_2(k2_yellow_1('#skF_2'),C_361,B_360)
      | ~ m1_subset_1(B_360,'#skF_2')
      | ~ m1_subset_1(C_361,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_1732,c_2087])).

tff(c_2370,plain,(
    ! [C_365,B_366] :
      ( k11_lattice3(k2_yellow_1('#skF_2'),C_365,k11_lattice3(k2_yellow_1('#skF_2'),C_365,B_366)) = k11_lattice3(k2_yellow_1('#skF_2'),C_365,B_366)
      | ~ m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'),C_365,B_366),'#skF_2')
      | ~ m1_subset_1(C_365,'#skF_2')
      | ~ m1_subset_1(B_366,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_1857,c_2093])).

tff(c_1549,plain,(
    ! [A_274,B_275,C_276] :
      ( r3_orders_2(A_274,B_275,C_276)
      | k12_lattice3(A_274,B_275,C_276) != B_275
      | ~ m1_subset_1(C_276,u1_struct_0(A_274))
      | ~ m1_subset_1(B_275,u1_struct_0(A_274))
      | ~ l1_orders_2(A_274)
      | ~ v2_lattice3(A_274)
      | ~ v5_orders_2(A_274)
      | ~ v3_orders_2(A_274) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_1556,plain,(
    ! [A_79,B_275,C_276] :
      ( r3_orders_2(k2_yellow_1(A_79),B_275,C_276)
      | k12_lattice3(k2_yellow_1(A_79),B_275,C_276) != B_275
      | ~ m1_subset_1(C_276,A_79)
      | ~ m1_subset_1(B_275,u1_struct_0(k2_yellow_1(A_79)))
      | ~ l1_orders_2(k2_yellow_1(A_79))
      | ~ v2_lattice3(k2_yellow_1(A_79))
      | ~ v5_orders_2(k2_yellow_1(A_79))
      | ~ v3_orders_2(k2_yellow_1(A_79)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_1549])).

tff(c_1561,plain,(
    ! [A_277,B_278,C_279] :
      ( r3_orders_2(k2_yellow_1(A_277),B_278,C_279)
      | k12_lattice3(k2_yellow_1(A_277),B_278,C_279) != B_278
      | ~ m1_subset_1(C_279,A_277)
      | ~ m1_subset_1(B_278,A_277)
      | ~ v2_lattice3(k2_yellow_1(A_277)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_50,c_42,c_52,c_1556])).

tff(c_58,plain,(
    ! [B_84,C_86,A_80] :
      ( r1_tarski(B_84,C_86)
      | ~ r3_orders_2(k2_yellow_1(A_80),B_84,C_86)
      | ~ m1_subset_1(C_86,u1_struct_0(k2_yellow_1(A_80)))
      | ~ m1_subset_1(B_84,u1_struct_0(k2_yellow_1(A_80)))
      | v1_xboole_0(A_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_71,plain,(
    ! [B_84,C_86,A_80] :
      ( r1_tarski(B_84,C_86)
      | ~ r3_orders_2(k2_yellow_1(A_80),B_84,C_86)
      | ~ m1_subset_1(C_86,A_80)
      | ~ m1_subset_1(B_84,A_80)
      | v1_xboole_0(A_80) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_52,c_58])).

tff(c_1566,plain,(
    ! [B_280,C_281,A_282] :
      ( r1_tarski(B_280,C_281)
      | v1_xboole_0(A_282)
      | k12_lattice3(k2_yellow_1(A_282),B_280,C_281) != B_280
      | ~ m1_subset_1(C_281,A_282)
      | ~ m1_subset_1(B_280,A_282)
      | ~ v2_lattice3(k2_yellow_1(A_282)) ) ),
    inference(resolution,[status(thm)],[c_1561,c_71])).

tff(c_1568,plain,(
    ! [B_270,C_271] :
      ( r1_tarski(B_270,C_271)
      | v1_xboole_0('#skF_2')
      | k11_lattice3(k2_yellow_1('#skF_2'),B_270,C_271) != B_270
      | ~ m1_subset_1(C_271,'#skF_2')
      | ~ m1_subset_1(B_270,'#skF_2')
      | ~ v2_lattice3(k2_yellow_1('#skF_2'))
      | ~ m1_subset_1(C_271,'#skF_2')
      | ~ m1_subset_1(B_270,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1539,c_1566])).

tff(c_1570,plain,(
    ! [B_270,C_271] :
      ( r1_tarski(B_270,C_271)
      | v1_xboole_0('#skF_2')
      | k11_lattice3(k2_yellow_1('#skF_2'),B_270,C_271) != B_270
      | ~ m1_subset_1(C_271,'#skF_2')
      | ~ m1_subset_1(B_270,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_1568])).

tff(c_1572,plain,(
    ! [B_283,C_284] :
      ( r1_tarski(B_283,C_284)
      | k11_lattice3(k2_yellow_1('#skF_2'),B_283,C_284) != B_283
      | ~ m1_subset_1(C_284,'#skF_2')
      | ~ m1_subset_1(B_283,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_1570])).

tff(c_1575,plain,(
    ! [B_263,C_262] :
      ( r1_tarski(B_263,C_262)
      | k11_lattice3(k2_yellow_1('#skF_2'),C_262,B_263) != B_263
      | ~ m1_subset_1(C_262,'#skF_2')
      | ~ m1_subset_1(B_263,'#skF_2')
      | ~ m1_subset_1(C_262,'#skF_2')
      | ~ m1_subset_1(B_263,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1424,c_1572])).

tff(c_2464,plain,(
    ! [C_367,B_368] :
      ( r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'),C_367,B_368),C_367)
      | ~ m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'),C_367,B_368),'#skF_2')
      | ~ m1_subset_1(C_367,'#skF_2')
      | ~ m1_subset_1(B_368,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2370,c_1575])).

tff(c_1425,plain,(
    ! [C_264,B_265] :
      ( k11_lattice3(k2_yellow_1('#skF_2'),C_264,B_265) = k11_lattice3(k2_yellow_1('#skF_2'),B_265,C_264)
      | ~ m1_subset_1(C_264,'#skF_2')
      | ~ m1_subset_1(B_265,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_66,c_1421])).

tff(c_152,plain,(
    ! [A_118,B_119,C_120] :
      ( m1_subset_1(k11_lattice3(A_118,B_119,C_120),u1_struct_0(A_118))
      | ~ m1_subset_1(C_120,u1_struct_0(A_118))
      | ~ m1_subset_1(B_119,u1_struct_0(A_118))
      | ~ l1_orders_2(A_118) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_155,plain,(
    ! [A_79,B_119,C_120] :
      ( m1_subset_1(k11_lattice3(k2_yellow_1(A_79),B_119,C_120),A_79)
      | ~ m1_subset_1(C_120,u1_struct_0(k2_yellow_1(A_79)))
      | ~ m1_subset_1(B_119,u1_struct_0(k2_yellow_1(A_79)))
      | ~ l1_orders_2(k2_yellow_1(A_79)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_152])).

tff(c_157,plain,(
    ! [A_79,B_119,C_120] :
      ( m1_subset_1(k11_lattice3(k2_yellow_1(A_79),B_119,C_120),A_79)
      | ~ m1_subset_1(C_120,A_79)
      | ~ m1_subset_1(B_119,A_79) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_52,c_52,c_155])).

tff(c_273,plain,(
    ! [A_140,B_141,C_142] :
      ( k12_lattice3(A_140,B_141,C_142) = B_141
      | ~ r3_orders_2(A_140,B_141,C_142)
      | ~ m1_subset_1(C_142,u1_struct_0(A_140))
      | ~ m1_subset_1(B_141,u1_struct_0(A_140))
      | ~ l1_orders_2(A_140)
      | ~ v2_lattice3(A_140)
      | ~ v5_orders_2(A_140)
      | ~ v3_orders_2(A_140) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_275,plain,(
    ! [A_80,B_84,C_86] :
      ( k12_lattice3(k2_yellow_1(A_80),B_84,C_86) = B_84
      | ~ m1_subset_1(C_86,u1_struct_0(k2_yellow_1(A_80)))
      | ~ m1_subset_1(B_84,u1_struct_0(k2_yellow_1(A_80)))
      | ~ l1_orders_2(k2_yellow_1(A_80))
      | ~ v2_lattice3(k2_yellow_1(A_80))
      | ~ v5_orders_2(k2_yellow_1(A_80))
      | ~ v3_orders_2(k2_yellow_1(A_80))
      | ~ r1_tarski(B_84,C_86)
      | ~ m1_subset_1(C_86,A_80)
      | ~ m1_subset_1(B_84,A_80)
      | v1_xboole_0(A_80) ) ),
    inference(resolution,[status(thm)],[c_72,c_273])).

tff(c_279,plain,(
    ! [A_143,B_144,C_145] :
      ( k12_lattice3(k2_yellow_1(A_143),B_144,C_145) = B_144
      | ~ v2_lattice3(k2_yellow_1(A_143))
      | ~ r1_tarski(B_144,C_145)
      | ~ m1_subset_1(C_145,A_143)
      | ~ m1_subset_1(B_144,A_143)
      | v1_xboole_0(A_143) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_50,c_42,c_52,c_52,c_275])).

tff(c_281,plain,(
    ! [B_144,C_145] :
      ( k12_lattice3(k2_yellow_1('#skF_2'),B_144,C_145) = B_144
      | ~ r1_tarski(B_144,C_145)
      | ~ m1_subset_1(C_145,'#skF_2')
      | ~ m1_subset_1(B_144,'#skF_2')
      | v1_xboole_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_66,c_279])).

tff(c_285,plain,(
    ! [B_146,C_147] :
      ( k12_lattice3(k2_yellow_1('#skF_2'),B_146,C_147) = B_146
      | ~ r1_tarski(B_146,C_147)
      | ~ m1_subset_1(C_147,'#skF_2')
      | ~ m1_subset_1(B_146,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_281])).

tff(c_248,plain,(
    ! [A_132,B_133,C_134] :
      ( k12_lattice3(A_132,B_133,C_134) = k11_lattice3(A_132,B_133,C_134)
      | ~ m1_subset_1(C_134,u1_struct_0(A_132))
      | ~ m1_subset_1(B_133,u1_struct_0(A_132))
      | ~ l1_orders_2(A_132)
      | ~ v2_lattice3(A_132)
      | ~ v5_orders_2(A_132) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_255,plain,(
    ! [A_79,B_133,C_134] :
      ( k12_lattice3(k2_yellow_1(A_79),B_133,C_134) = k11_lattice3(k2_yellow_1(A_79),B_133,C_134)
      | ~ m1_subset_1(C_134,A_79)
      | ~ m1_subset_1(B_133,u1_struct_0(k2_yellow_1(A_79)))
      | ~ l1_orders_2(k2_yellow_1(A_79))
      | ~ v2_lattice3(k2_yellow_1(A_79))
      | ~ v5_orders_2(k2_yellow_1(A_79)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_248])).

tff(c_260,plain,(
    ! [A_135,B_136,C_137] :
      ( k12_lattice3(k2_yellow_1(A_135),B_136,C_137) = k11_lattice3(k2_yellow_1(A_135),B_136,C_137)
      | ~ m1_subset_1(C_137,A_135)
      | ~ m1_subset_1(B_136,A_135)
      | ~ v2_lattice3(k2_yellow_1(A_135)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_42,c_52,c_255])).

tff(c_263,plain,(
    ! [B_136,C_137] :
      ( k12_lattice3(k2_yellow_1('#skF_2'),B_136,C_137) = k11_lattice3(k2_yellow_1('#skF_2'),B_136,C_137)
      | ~ m1_subset_1(C_137,'#skF_2')
      | ~ m1_subset_1(B_136,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_66,c_260])).

tff(c_291,plain,(
    ! [B_146,C_147] :
      ( k11_lattice3(k2_yellow_1('#skF_2'),B_146,C_147) = B_146
      | ~ m1_subset_1(C_147,'#skF_2')
      | ~ m1_subset_1(B_146,'#skF_2')
      | ~ r1_tarski(B_146,C_147)
      | ~ m1_subset_1(C_147,'#skF_2')
      | ~ m1_subset_1(B_146,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_285,c_263])).

tff(c_487,plain,(
    ! [A_172,B_173,C_174] :
      ( r1_orders_2(A_172,k11_lattice3(A_172,B_173,C_174),B_173)
      | ~ m1_subset_1(k11_lattice3(A_172,B_173,C_174),u1_struct_0(A_172))
      | ~ m1_subset_1(C_174,u1_struct_0(A_172))
      | ~ m1_subset_1(B_173,u1_struct_0(A_172))
      | ~ l1_orders_2(A_172)
      | ~ v2_lattice3(A_172)
      | ~ v5_orders_2(A_172)
      | v2_struct_0(A_172) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_491,plain,(
    ! [B_146,C_147] :
      ( r1_orders_2(k2_yellow_1('#skF_2'),k11_lattice3(k2_yellow_1('#skF_2'),B_146,C_147),B_146)
      | ~ m1_subset_1(B_146,u1_struct_0(k2_yellow_1('#skF_2')))
      | ~ m1_subset_1(C_147,u1_struct_0(k2_yellow_1('#skF_2')))
      | ~ m1_subset_1(B_146,u1_struct_0(k2_yellow_1('#skF_2')))
      | ~ l1_orders_2(k2_yellow_1('#skF_2'))
      | ~ v2_lattice3(k2_yellow_1('#skF_2'))
      | ~ v5_orders_2(k2_yellow_1('#skF_2'))
      | v2_struct_0(k2_yellow_1('#skF_2'))
      | ~ m1_subset_1(C_147,'#skF_2')
      | ~ m1_subset_1(B_146,'#skF_2')
      | ~ r1_tarski(B_146,C_147)
      | ~ m1_subset_1(C_147,'#skF_2')
      | ~ m1_subset_1(B_146,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_291,c_487])).

tff(c_503,plain,(
    ! [B_146,C_147] :
      ( r1_orders_2(k2_yellow_1('#skF_2'),k11_lattice3(k2_yellow_1('#skF_2'),B_146,C_147),B_146)
      | v2_struct_0(k2_yellow_1('#skF_2'))
      | ~ r1_tarski(B_146,C_147)
      | ~ m1_subset_1(C_147,'#skF_2')
      | ~ m1_subset_1(B_146,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_66,c_42,c_52,c_52,c_52,c_491])).

tff(c_511,plain,(
    v2_struct_0(k2_yellow_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_503])).

tff(c_514,plain,
    ( ~ v2_lattice3(k2_yellow_1('#skF_2'))
    | ~ l1_orders_2(k2_yellow_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_511,c_14])).

tff(c_518,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_66,c_514])).

tff(c_520,plain,(
    ~ v2_struct_0(k2_yellow_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_503])).

tff(c_159,plain,(
    ! [A_124,C_125,B_126] :
      ( k11_lattice3(A_124,C_125,B_126) = k11_lattice3(A_124,B_126,C_125)
      | ~ m1_subset_1(C_125,u1_struct_0(A_124))
      | ~ m1_subset_1(B_126,u1_struct_0(A_124))
      | ~ l1_orders_2(A_124)
      | ~ v2_lattice3(A_124)
      | ~ v5_orders_2(A_124) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_166,plain,(
    ! [A_79,C_125,B_126] :
      ( k11_lattice3(k2_yellow_1(A_79),C_125,B_126) = k11_lattice3(k2_yellow_1(A_79),B_126,C_125)
      | ~ m1_subset_1(C_125,A_79)
      | ~ m1_subset_1(B_126,u1_struct_0(k2_yellow_1(A_79)))
      | ~ l1_orders_2(k2_yellow_1(A_79))
      | ~ v2_lattice3(k2_yellow_1(A_79))
      | ~ v5_orders_2(k2_yellow_1(A_79)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_159])).

tff(c_171,plain,(
    ! [A_127,C_128,B_129] :
      ( k11_lattice3(k2_yellow_1(A_127),C_128,B_129) = k11_lattice3(k2_yellow_1(A_127),B_129,C_128)
      | ~ m1_subset_1(C_128,A_127)
      | ~ m1_subset_1(B_129,A_127)
      | ~ v2_lattice3(k2_yellow_1(A_127)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_42,c_52,c_166])).

tff(c_174,plain,(
    ! [C_128,B_129] :
      ( k11_lattice3(k2_yellow_1('#skF_2'),C_128,B_129) = k11_lattice3(k2_yellow_1('#skF_2'),B_129,C_128)
      | ~ m1_subset_1(C_128,'#skF_2')
      | ~ m1_subset_1(B_129,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_66,c_171])).

tff(c_548,plain,(
    ! [A_179,B_180,C_181] :
      ( r1_orders_2(A_179,k11_lattice3(A_179,B_180,C_181),B_180)
      | ~ v2_lattice3(A_179)
      | ~ v5_orders_2(A_179)
      | v2_struct_0(A_179)
      | ~ m1_subset_1(C_181,u1_struct_0(A_179))
      | ~ m1_subset_1(B_180,u1_struct_0(A_179))
      | ~ l1_orders_2(A_179) ) ),
    inference(resolution,[status(thm)],[c_16,c_487])).

tff(c_557,plain,(
    ! [C_128,B_129] :
      ( r1_orders_2(k2_yellow_1('#skF_2'),k11_lattice3(k2_yellow_1('#skF_2'),C_128,B_129),B_129)
      | ~ v2_lattice3(k2_yellow_1('#skF_2'))
      | ~ v5_orders_2(k2_yellow_1('#skF_2'))
      | v2_struct_0(k2_yellow_1('#skF_2'))
      | ~ m1_subset_1(C_128,u1_struct_0(k2_yellow_1('#skF_2')))
      | ~ m1_subset_1(B_129,u1_struct_0(k2_yellow_1('#skF_2')))
      | ~ l1_orders_2(k2_yellow_1('#skF_2'))
      | ~ m1_subset_1(C_128,'#skF_2')
      | ~ m1_subset_1(B_129,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_174,c_548])).

tff(c_568,plain,(
    ! [C_128,B_129] :
      ( r1_orders_2(k2_yellow_1('#skF_2'),k11_lattice3(k2_yellow_1('#skF_2'),C_128,B_129),B_129)
      | v2_struct_0(k2_yellow_1('#skF_2'))
      | ~ m1_subset_1(C_128,'#skF_2')
      | ~ m1_subset_1(B_129,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_52,c_52,c_50,c_66,c_557])).

tff(c_569,plain,(
    ! [C_128,B_129] :
      ( r1_orders_2(k2_yellow_1('#skF_2'),k11_lattice3(k2_yellow_1('#skF_2'),C_128,B_129),B_129)
      | ~ m1_subset_1(C_128,'#skF_2')
      | ~ m1_subset_1(B_129,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_520,c_568])).

tff(c_300,plain,(
    ! [B_148,C_149] :
      ( k11_lattice3(k2_yellow_1('#skF_2'),B_148,C_149) = B_148
      | ~ m1_subset_1(C_149,'#skF_2')
      | ~ m1_subset_1(B_148,'#skF_2')
      | ~ r1_tarski(B_148,C_149)
      | ~ m1_subset_1(C_149,'#skF_2')
      | ~ m1_subset_1(B_148,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_285,c_263])).

tff(c_315,plain,(
    ! [C_149,B_148] :
      ( k11_lattice3(k2_yellow_1('#skF_2'),C_149,B_148) = B_148
      | ~ m1_subset_1(C_149,'#skF_2')
      | ~ m1_subset_1(B_148,'#skF_2')
      | ~ m1_subset_1(C_149,'#skF_2')
      | ~ m1_subset_1(B_148,'#skF_2')
      | ~ r1_tarski(B_148,C_149)
      | ~ m1_subset_1(C_149,'#skF_2')
      | ~ m1_subset_1(B_148,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_300,c_174])).

tff(c_551,plain,(
    ! [B_148,C_149] :
      ( r1_orders_2(k2_yellow_1('#skF_2'),B_148,C_149)
      | ~ v2_lattice3(k2_yellow_1('#skF_2'))
      | ~ v5_orders_2(k2_yellow_1('#skF_2'))
      | v2_struct_0(k2_yellow_1('#skF_2'))
      | ~ m1_subset_1(B_148,u1_struct_0(k2_yellow_1('#skF_2')))
      | ~ m1_subset_1(C_149,u1_struct_0(k2_yellow_1('#skF_2')))
      | ~ l1_orders_2(k2_yellow_1('#skF_2'))
      | ~ m1_subset_1(C_149,'#skF_2')
      | ~ m1_subset_1(B_148,'#skF_2')
      | ~ m1_subset_1(C_149,'#skF_2')
      | ~ m1_subset_1(B_148,'#skF_2')
      | ~ r1_tarski(B_148,C_149)
      | ~ m1_subset_1(C_149,'#skF_2')
      | ~ m1_subset_1(B_148,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_315,c_548])).

tff(c_562,plain,(
    ! [B_148,C_149] :
      ( r1_orders_2(k2_yellow_1('#skF_2'),B_148,C_149)
      | v2_struct_0(k2_yellow_1('#skF_2'))
      | ~ r1_tarski(B_148,C_149)
      | ~ m1_subset_1(C_149,'#skF_2')
      | ~ m1_subset_1(B_148,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_52,c_52,c_50,c_66,c_551])).

tff(c_563,plain,(
    ! [B_148,C_149] :
      ( r1_orders_2(k2_yellow_1('#skF_2'),B_148,C_149)
      | ~ r1_tarski(B_148,C_149)
      | ~ m1_subset_1(C_149,'#skF_2')
      | ~ m1_subset_1(B_148,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_520,c_562])).

tff(c_880,plain,(
    ! [A_218,B_219,C_220,D_221] :
      ( r1_orders_2(A_218,'#skF_1'(A_218,B_219,C_220,D_221),C_220)
      | k11_lattice3(A_218,B_219,C_220) = D_221
      | ~ r1_orders_2(A_218,D_221,C_220)
      | ~ r1_orders_2(A_218,D_221,B_219)
      | ~ m1_subset_1(D_221,u1_struct_0(A_218))
      | ~ m1_subset_1(C_220,u1_struct_0(A_218))
      | ~ m1_subset_1(B_219,u1_struct_0(A_218))
      | ~ l1_orders_2(A_218)
      | ~ v2_lattice3(A_218)
      | ~ v5_orders_2(A_218)
      | v2_struct_0(A_218) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_18,plain,(
    ! [A_14,B_38,C_50,D_56] :
      ( ~ r1_orders_2(A_14,'#skF_1'(A_14,B_38,C_50,D_56),D_56)
      | k11_lattice3(A_14,B_38,C_50) = D_56
      | ~ r1_orders_2(A_14,D_56,C_50)
      | ~ r1_orders_2(A_14,D_56,B_38)
      | ~ m1_subset_1(D_56,u1_struct_0(A_14))
      | ~ m1_subset_1(C_50,u1_struct_0(A_14))
      | ~ m1_subset_1(B_38,u1_struct_0(A_14))
      | ~ l1_orders_2(A_14)
      | ~ v2_lattice3(A_14)
      | ~ v5_orders_2(A_14)
      | v2_struct_0(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_1115,plain,(
    ! [A_228,B_229,C_230] :
      ( k11_lattice3(A_228,B_229,C_230) = C_230
      | ~ r1_orders_2(A_228,C_230,C_230)
      | ~ r1_orders_2(A_228,C_230,B_229)
      | ~ m1_subset_1(C_230,u1_struct_0(A_228))
      | ~ m1_subset_1(B_229,u1_struct_0(A_228))
      | ~ l1_orders_2(A_228)
      | ~ v2_lattice3(A_228)
      | ~ v5_orders_2(A_228)
      | v2_struct_0(A_228) ) ),
    inference(resolution,[status(thm)],[c_880,c_18])).

tff(c_1118,plain,(
    ! [B_229,C_149] :
      ( k11_lattice3(k2_yellow_1('#skF_2'),B_229,C_149) = C_149
      | ~ r1_orders_2(k2_yellow_1('#skF_2'),C_149,B_229)
      | ~ m1_subset_1(C_149,u1_struct_0(k2_yellow_1('#skF_2')))
      | ~ m1_subset_1(B_229,u1_struct_0(k2_yellow_1('#skF_2')))
      | ~ l1_orders_2(k2_yellow_1('#skF_2'))
      | ~ v2_lattice3(k2_yellow_1('#skF_2'))
      | ~ v5_orders_2(k2_yellow_1('#skF_2'))
      | v2_struct_0(k2_yellow_1('#skF_2'))
      | ~ r1_tarski(C_149,C_149)
      | ~ m1_subset_1(C_149,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_563,c_1115])).

tff(c_1123,plain,(
    ! [B_229,C_149] :
      ( k11_lattice3(k2_yellow_1('#skF_2'),B_229,C_149) = C_149
      | ~ r1_orders_2(k2_yellow_1('#skF_2'),C_149,B_229)
      | ~ m1_subset_1(B_229,'#skF_2')
      | v2_struct_0(k2_yellow_1('#skF_2'))
      | ~ m1_subset_1(C_149,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_50,c_66,c_42,c_52,c_52,c_1118])).

tff(c_1129,plain,(
    ! [B_231,C_232] :
      ( k11_lattice3(k2_yellow_1('#skF_2'),B_231,C_232) = C_232
      | ~ r1_orders_2(k2_yellow_1('#skF_2'),C_232,B_231)
      | ~ m1_subset_1(B_231,'#skF_2')
      | ~ m1_subset_1(C_232,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_520,c_1123])).

tff(c_1209,plain,(
    ! [B_237,C_238] :
      ( k11_lattice3(k2_yellow_1('#skF_2'),B_237,k11_lattice3(k2_yellow_1('#skF_2'),C_238,B_237)) = k11_lattice3(k2_yellow_1('#skF_2'),C_238,B_237)
      | ~ m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'),C_238,B_237),'#skF_2')
      | ~ m1_subset_1(C_238,'#skF_2')
      | ~ m1_subset_1(B_237,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_569,c_1129])).

tff(c_350,plain,(
    ! [A_150,B_151,C_152] :
      ( r3_orders_2(A_150,B_151,C_152)
      | k12_lattice3(A_150,B_151,C_152) != B_151
      | ~ m1_subset_1(C_152,u1_struct_0(A_150))
      | ~ m1_subset_1(B_151,u1_struct_0(A_150))
      | ~ l1_orders_2(A_150)
      | ~ v2_lattice3(A_150)
      | ~ v5_orders_2(A_150)
      | ~ v3_orders_2(A_150) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_357,plain,(
    ! [A_79,B_151,C_152] :
      ( r3_orders_2(k2_yellow_1(A_79),B_151,C_152)
      | k12_lattice3(k2_yellow_1(A_79),B_151,C_152) != B_151
      | ~ m1_subset_1(C_152,A_79)
      | ~ m1_subset_1(B_151,u1_struct_0(k2_yellow_1(A_79)))
      | ~ l1_orders_2(k2_yellow_1(A_79))
      | ~ v2_lattice3(k2_yellow_1(A_79))
      | ~ v5_orders_2(k2_yellow_1(A_79))
      | ~ v3_orders_2(k2_yellow_1(A_79)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_350])).

tff(c_362,plain,(
    ! [A_153,B_154,C_155] :
      ( r3_orders_2(k2_yellow_1(A_153),B_154,C_155)
      | k12_lattice3(k2_yellow_1(A_153),B_154,C_155) != B_154
      | ~ m1_subset_1(C_155,A_153)
      | ~ m1_subset_1(B_154,A_153)
      | ~ v2_lattice3(k2_yellow_1(A_153)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_50,c_42,c_52,c_357])).

tff(c_372,plain,(
    ! [B_156,C_157,A_158] :
      ( r1_tarski(B_156,C_157)
      | v1_xboole_0(A_158)
      | k12_lattice3(k2_yellow_1(A_158),B_156,C_157) != B_156
      | ~ m1_subset_1(C_157,A_158)
      | ~ m1_subset_1(B_156,A_158)
      | ~ v2_lattice3(k2_yellow_1(A_158)) ) ),
    inference(resolution,[status(thm)],[c_362,c_71])).

tff(c_376,plain,(
    ! [B_136,C_137] :
      ( r1_tarski(B_136,C_137)
      | v1_xboole_0('#skF_2')
      | k11_lattice3(k2_yellow_1('#skF_2'),B_136,C_137) != B_136
      | ~ m1_subset_1(C_137,'#skF_2')
      | ~ m1_subset_1(B_136,'#skF_2')
      | ~ v2_lattice3(k2_yellow_1('#skF_2'))
      | ~ m1_subset_1(C_137,'#skF_2')
      | ~ m1_subset_1(B_136,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_263,c_372])).

tff(c_382,plain,(
    ! [B_136,C_137] :
      ( r1_tarski(B_136,C_137)
      | v1_xboole_0('#skF_2')
      | k11_lattice3(k2_yellow_1('#skF_2'),B_136,C_137) != B_136
      | ~ m1_subset_1(C_137,'#skF_2')
      | ~ m1_subset_1(B_136,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_376])).

tff(c_384,plain,(
    ! [B_159,C_160] :
      ( r1_tarski(B_159,C_160)
      | k11_lattice3(k2_yellow_1('#skF_2'),B_159,C_160) != B_159
      | ~ m1_subset_1(C_160,'#skF_2')
      | ~ m1_subset_1(B_159,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_382])).

tff(c_390,plain,(
    ! [B_129,C_128] :
      ( r1_tarski(B_129,C_128)
      | k11_lattice3(k2_yellow_1('#skF_2'),C_128,B_129) != B_129
      | ~ m1_subset_1(C_128,'#skF_2')
      | ~ m1_subset_1(B_129,'#skF_2')
      | ~ m1_subset_1(C_128,'#skF_2')
      | ~ m1_subset_1(B_129,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_174,c_384])).

tff(c_1300,plain,(
    ! [C_239,B_240] :
      ( r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'),C_239,B_240),B_240)
      | ~ m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'),C_239,B_240),'#skF_2')
      | ~ m1_subset_1(C_239,'#skF_2')
      | ~ m1_subset_1(B_240,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1209,c_390])).

tff(c_175,plain,(
    ! [C_130,B_131] :
      ( k11_lattice3(k2_yellow_1('#skF_2'),C_130,B_131) = k11_lattice3(k2_yellow_1('#skF_2'),B_131,C_130)
      | ~ m1_subset_1(C_130,'#skF_2')
      | ~ m1_subset_1(B_131,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_66,c_171])).

tff(c_125,plain,(
    ! [A_106,B_107,C_108] :
      ( r1_tarski(A_106,k3_xboole_0(B_107,C_108))
      | ~ r1_tarski(A_106,C_108)
      | ~ r1_tarski(A_106,B_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_60,plain,(
    ~ r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4'),k3_xboole_0('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_132,plain,
    ( ~ r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4'),'#skF_4')
    | ~ r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_125,c_60])).

tff(c_133,plain,(
    ~ r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_132])).

tff(c_202,plain,
    ( ~ r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'),'#skF_4','#skF_3'),'#skF_3')
    | ~ m1_subset_1('#skF_4','#skF_2')
    | ~ m1_subset_1('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_175,c_133])).

tff(c_233,plain,(
    ~ r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'),'#skF_4','#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_70,c_202])).

tff(c_1303,plain,
    ( ~ m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'),'#skF_4','#skF_3'),'#skF_2')
    | ~ m1_subset_1('#skF_4','#skF_2')
    | ~ m1_subset_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_1300,c_233])).

tff(c_1326,plain,(
    ~ m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'),'#skF_4','#skF_3'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_70,c_1303])).

tff(c_1369,plain,
    ( ~ m1_subset_1('#skF_3','#skF_2')
    | ~ m1_subset_1('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_157,c_1326])).

tff(c_1377,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_69,c_1369])).

tff(c_1378,plain,(
    ~ r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_132])).

tff(c_1464,plain,
    ( ~ r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'),'#skF_4','#skF_3'),'#skF_4')
    | ~ m1_subset_1('#skF_4','#skF_2')
    | ~ m1_subset_1('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1425,c_1378])).

tff(c_1503,plain,(
    ~ r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'),'#skF_4','#skF_3'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_70,c_1464])).

tff(c_2467,plain,
    ( ~ m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'),'#skF_4','#skF_3'),'#skF_2')
    | ~ m1_subset_1('#skF_4','#skF_2')
    | ~ m1_subset_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_2464,c_1503])).

tff(c_2490,plain,(
    ~ m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'),'#skF_4','#skF_3'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_70,c_2467])).

tff(c_2502,plain,
    ( ~ m1_subset_1('#skF_3','#skF_2')
    | ~ m1_subset_1('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_1407,c_2490])).

tff(c_2510,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_69,c_2502])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.15  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.36  % Computer   : n008.cluster.edu
% 0.15/0.36  % Model      : x86_64 x86_64
% 0.15/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.36  % Memory     : 8042.1875MB
% 0.15/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.36  % CPULimit   : 60
% 0.15/0.36  % DateTime   : Tue Dec  1 12:03:45 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.15/0.37  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.57/1.82  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.78/1.84  
% 4.78/1.84  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.78/1.84  %$ r3_orders_2 > r1_orders_2 > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v2_lattice3 > v1_xboole_0 > v1_orders_2 > l1_orders_2 > k2_enumset1 > k12_lattice3 > k11_lattice3 > k3_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > u1_orders_2 > k2_yellow_1 > k1_yellow_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 4.78/1.84  
% 4.78/1.84  %Foreground sorts:
% 4.78/1.84  
% 4.78/1.84  
% 4.78/1.84  %Background operators:
% 4.78/1.84  
% 4.78/1.84  
% 4.78/1.84  %Foreground operators:
% 4.78/1.84  tff(v1_orders_2, type, v1_orders_2: $i > $o).
% 4.78/1.84  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.78/1.84  tff(r3_orders_2, type, r3_orders_2: ($i * $i * $i) > $o).
% 4.78/1.84  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 4.78/1.84  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.78/1.84  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 4.78/1.84  tff(k2_yellow_1, type, k2_yellow_1: $i > $i).
% 4.78/1.84  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.78/1.84  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.78/1.84  tff(k11_lattice3, type, k11_lattice3: ($i * $i * $i) > $i).
% 4.78/1.84  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.78/1.84  tff(k12_lattice3, type, k12_lattice3: ($i * $i * $i) > $i).
% 4.78/1.84  tff('#skF_2', type, '#skF_2': $i).
% 4.78/1.84  tff('#skF_3', type, '#skF_3': $i).
% 4.78/1.84  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 4.78/1.84  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 4.78/1.84  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 4.78/1.84  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.78/1.84  tff('#skF_4', type, '#skF_4': $i).
% 4.78/1.84  tff(k1_yellow_1, type, k1_yellow_1: $i > $i).
% 4.78/1.84  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.78/1.84  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.78/1.84  tff(v2_lattice3, type, v2_lattice3: $i > $o).
% 4.78/1.84  tff(u1_orders_2, type, u1_orders_2: $i > $i).
% 4.78/1.84  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 4.78/1.84  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.78/1.84  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.78/1.84  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.78/1.84  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 4.78/1.84  
% 4.89/1.87  tff(f_149, axiom, (![A]: ((u1_struct_0(k2_yellow_1(A)) = A) & (u1_orders_2(k2_yellow_1(A)) = k1_yellow_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_yellow_1)).
% 4.89/1.87  tff(f_176, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (v2_lattice3(k2_yellow_1(A)) => (![B]: (m1_subset_1(B, u1_struct_0(k2_yellow_1(A))) => (![C]: (m1_subset_1(C, u1_struct_0(k2_yellow_1(A))) => r1_tarski(k11_lattice3(k2_yellow_1(A), B, C), k3_xboole_0(B, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_yellow_1)).
% 4.89/1.87  tff(f_137, axiom, (![A]: (v1_orders_2(k2_yellow_1(A)) & l1_orders_2(k2_yellow_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_yellow_1)).
% 4.89/1.87  tff(f_56, axiom, (![A, B, C]: (((l1_orders_2(A) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => m1_subset_1(k11_lattice3(A, B, C), u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k11_lattice3)).
% 4.89/1.87  tff(f_145, axiom, (![A]: (((v1_orders_2(k2_yellow_1(A)) & v3_orders_2(k2_yellow_1(A))) & v4_orders_2(k2_yellow_1(A))) & v5_orders_2(k2_yellow_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc5_yellow_1)).
% 4.89/1.87  tff(f_162, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (m1_subset_1(B, u1_struct_0(k2_yellow_1(A))) => (![C]: (m1_subset_1(C, u1_struct_0(k2_yellow_1(A))) => (r3_orders_2(k2_yellow_1(A), B, C) <=> r1_tarski(B, C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_yellow_1)).
% 4.89/1.87  tff(f_133, axiom, (![A]: ((((v3_orders_2(A) & v5_orders_2(A)) & v2_lattice3(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => ((B = k12_lattice3(A, B, C)) <=> r3_orders_2(A, B, C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_yellow_0)).
% 4.89/1.87  tff(f_101, axiom, (![A, B, C]: (((((v5_orders_2(A) & v2_lattice3(A)) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (k12_lattice3(A, B, C) = k11_lattice3(A, B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k12_lattice3)).
% 4.89/1.87  tff(f_89, axiom, (![A]: ((((~v2_struct_0(A) & v5_orders_2(A)) & v2_lattice3(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => ((D = k11_lattice3(A, B, C)) <=> ((r1_orders_2(A, D, B) & r1_orders_2(A, D, C)) & (![E]: (m1_subset_1(E, u1_struct_0(A)) => ((r1_orders_2(A, E, B) & r1_orders_2(A, E, C)) => r1_orders_2(A, E, D)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l28_lattice3)).
% 4.89/1.87  tff(f_48, axiom, (![A]: (l1_orders_2(A) => (v2_lattice3(A) => ~v2_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_lattice3)).
% 4.89/1.87  tff(f_115, axiom, (![A]: (((v5_orders_2(A) & v2_lattice3(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (k11_lattice3(A, B, C) = k11_lattice3(A, C, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t15_lattice3)).
% 4.89/1.87  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.89/1.87  tff(f_37, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(A, C)) => r1_tarski(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_xboole_1)).
% 4.89/1.87  tff(c_52, plain, (![A_79]: (u1_struct_0(k2_yellow_1(A_79))=A_79)), inference(cnfTransformation, [status(thm)], [f_149])).
% 4.89/1.87  tff(c_62, plain, (m1_subset_1('#skF_4', u1_struct_0(k2_yellow_1('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_176])).
% 4.89/1.87  tff(c_70, plain, (m1_subset_1('#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_62])).
% 4.89/1.87  tff(c_64, plain, (m1_subset_1('#skF_3', u1_struct_0(k2_yellow_1('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_176])).
% 4.89/1.87  tff(c_69, plain, (m1_subset_1('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_64])).
% 4.89/1.87  tff(c_42, plain, (![A_77]: (l1_orders_2(k2_yellow_1(A_77)))), inference(cnfTransformation, [status(thm)], [f_137])).
% 4.89/1.87  tff(c_1402, plain, (![A_252, B_253, C_254]: (m1_subset_1(k11_lattice3(A_252, B_253, C_254), u1_struct_0(A_252)) | ~m1_subset_1(C_254, u1_struct_0(A_252)) | ~m1_subset_1(B_253, u1_struct_0(A_252)) | ~l1_orders_2(A_252))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.89/1.87  tff(c_1405, plain, (![A_79, B_253, C_254]: (m1_subset_1(k11_lattice3(k2_yellow_1(A_79), B_253, C_254), A_79) | ~m1_subset_1(C_254, u1_struct_0(k2_yellow_1(A_79))) | ~m1_subset_1(B_253, u1_struct_0(k2_yellow_1(A_79))) | ~l1_orders_2(k2_yellow_1(A_79)))), inference(superposition, [status(thm), theory('equality')], [c_52, c_1402])).
% 4.89/1.87  tff(c_1407, plain, (![A_79, B_253, C_254]: (m1_subset_1(k11_lattice3(k2_yellow_1(A_79), B_253, C_254), A_79) | ~m1_subset_1(C_254, A_79) | ~m1_subset_1(B_253, A_79))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_52, c_52, c_1405])).
% 4.89/1.87  tff(c_66, plain, (v2_lattice3(k2_yellow_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_176])).
% 4.89/1.87  tff(c_50, plain, (![A_78]: (v5_orders_2(k2_yellow_1(A_78)))), inference(cnfTransformation, [status(thm)], [f_145])).
% 4.89/1.87  tff(c_68, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_176])).
% 4.89/1.87  tff(c_46, plain, (![A_78]: (v3_orders_2(k2_yellow_1(A_78)))), inference(cnfTransformation, [status(thm)], [f_145])).
% 4.89/1.87  tff(c_56, plain, (![A_80, B_84, C_86]: (r3_orders_2(k2_yellow_1(A_80), B_84, C_86) | ~r1_tarski(B_84, C_86) | ~m1_subset_1(C_86, u1_struct_0(k2_yellow_1(A_80))) | ~m1_subset_1(B_84, u1_struct_0(k2_yellow_1(A_80))) | v1_xboole_0(A_80))), inference(cnfTransformation, [status(thm)], [f_162])).
% 4.89/1.87  tff(c_72, plain, (![A_80, B_84, C_86]: (r3_orders_2(k2_yellow_1(A_80), B_84, C_86) | ~r1_tarski(B_84, C_86) | ~m1_subset_1(C_86, A_80) | ~m1_subset_1(B_84, A_80) | v1_xboole_0(A_80))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_52, c_56])).
% 4.89/1.87  tff(c_1586, plain, (![A_287, B_288, C_289]: (k12_lattice3(A_287, B_288, C_289)=B_288 | ~r3_orders_2(A_287, B_288, C_289) | ~m1_subset_1(C_289, u1_struct_0(A_287)) | ~m1_subset_1(B_288, u1_struct_0(A_287)) | ~l1_orders_2(A_287) | ~v2_lattice3(A_287) | ~v5_orders_2(A_287) | ~v3_orders_2(A_287))), inference(cnfTransformation, [status(thm)], [f_133])).
% 4.89/1.87  tff(c_1590, plain, (![A_80, B_84, C_86]: (k12_lattice3(k2_yellow_1(A_80), B_84, C_86)=B_84 | ~m1_subset_1(C_86, u1_struct_0(k2_yellow_1(A_80))) | ~m1_subset_1(B_84, u1_struct_0(k2_yellow_1(A_80))) | ~l1_orders_2(k2_yellow_1(A_80)) | ~v2_lattice3(k2_yellow_1(A_80)) | ~v5_orders_2(k2_yellow_1(A_80)) | ~v3_orders_2(k2_yellow_1(A_80)) | ~r1_tarski(B_84, C_86) | ~m1_subset_1(C_86, A_80) | ~m1_subset_1(B_84, A_80) | v1_xboole_0(A_80))), inference(resolution, [status(thm)], [c_72, c_1586])).
% 4.89/1.87  tff(c_1597, plain, (![A_290, B_291, C_292]: (k12_lattice3(k2_yellow_1(A_290), B_291, C_292)=B_291 | ~v2_lattice3(k2_yellow_1(A_290)) | ~r1_tarski(B_291, C_292) | ~m1_subset_1(C_292, A_290) | ~m1_subset_1(B_291, A_290) | v1_xboole_0(A_290))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_50, c_42, c_52, c_52, c_1590])).
% 4.89/1.87  tff(c_1599, plain, (![B_291, C_292]: (k12_lattice3(k2_yellow_1('#skF_2'), B_291, C_292)=B_291 | ~r1_tarski(B_291, C_292) | ~m1_subset_1(C_292, '#skF_2') | ~m1_subset_1(B_291, '#skF_2') | v1_xboole_0('#skF_2'))), inference(resolution, [status(thm)], [c_66, c_1597])).
% 4.89/1.87  tff(c_1603, plain, (![B_293, C_294]: (k12_lattice3(k2_yellow_1('#skF_2'), B_293, C_294)=B_293 | ~r1_tarski(B_293, C_294) | ~m1_subset_1(C_294, '#skF_2') | ~m1_subset_1(B_293, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_68, c_1599])).
% 4.89/1.87  tff(c_1518, plain, (![A_266, B_267, C_268]: (k12_lattice3(A_266, B_267, C_268)=k11_lattice3(A_266, B_267, C_268) | ~m1_subset_1(C_268, u1_struct_0(A_266)) | ~m1_subset_1(B_267, u1_struct_0(A_266)) | ~l1_orders_2(A_266) | ~v2_lattice3(A_266) | ~v5_orders_2(A_266))), inference(cnfTransformation, [status(thm)], [f_101])).
% 4.89/1.87  tff(c_1525, plain, (![A_79, B_267, C_268]: (k12_lattice3(k2_yellow_1(A_79), B_267, C_268)=k11_lattice3(k2_yellow_1(A_79), B_267, C_268) | ~m1_subset_1(C_268, A_79) | ~m1_subset_1(B_267, u1_struct_0(k2_yellow_1(A_79))) | ~l1_orders_2(k2_yellow_1(A_79)) | ~v2_lattice3(k2_yellow_1(A_79)) | ~v5_orders_2(k2_yellow_1(A_79)))), inference(superposition, [status(thm), theory('equality')], [c_52, c_1518])).
% 4.89/1.87  tff(c_1536, plain, (![A_269, B_270, C_271]: (k12_lattice3(k2_yellow_1(A_269), B_270, C_271)=k11_lattice3(k2_yellow_1(A_269), B_270, C_271) | ~m1_subset_1(C_271, A_269) | ~m1_subset_1(B_270, A_269) | ~v2_lattice3(k2_yellow_1(A_269)))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_42, c_52, c_1525])).
% 4.89/1.87  tff(c_1539, plain, (![B_270, C_271]: (k12_lattice3(k2_yellow_1('#skF_2'), B_270, C_271)=k11_lattice3(k2_yellow_1('#skF_2'), B_270, C_271) | ~m1_subset_1(C_271, '#skF_2') | ~m1_subset_1(B_270, '#skF_2'))), inference(resolution, [status(thm)], [c_66, c_1536])).
% 4.89/1.87  tff(c_1611, plain, (![B_293, C_294]: (k11_lattice3(k2_yellow_1('#skF_2'), B_293, C_294)=B_293 | ~m1_subset_1(C_294, '#skF_2') | ~m1_subset_1(B_293, '#skF_2') | ~r1_tarski(B_293, C_294) | ~m1_subset_1(C_294, '#skF_2') | ~m1_subset_1(B_293, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_1603, c_1539])).
% 4.89/1.87  tff(c_1703, plain, (![A_297, B_298, C_299]: (r1_orders_2(A_297, k11_lattice3(A_297, B_298, C_299), B_298) | ~m1_subset_1(k11_lattice3(A_297, B_298, C_299), u1_struct_0(A_297)) | ~m1_subset_1(C_299, u1_struct_0(A_297)) | ~m1_subset_1(B_298, u1_struct_0(A_297)) | ~l1_orders_2(A_297) | ~v2_lattice3(A_297) | ~v5_orders_2(A_297) | v2_struct_0(A_297))), inference(cnfTransformation, [status(thm)], [f_89])).
% 4.89/1.87  tff(c_1705, plain, (![B_293, C_294]: (r1_orders_2(k2_yellow_1('#skF_2'), k11_lattice3(k2_yellow_1('#skF_2'), B_293, C_294), B_293) | ~m1_subset_1(B_293, u1_struct_0(k2_yellow_1('#skF_2'))) | ~m1_subset_1(C_294, u1_struct_0(k2_yellow_1('#skF_2'))) | ~m1_subset_1(B_293, u1_struct_0(k2_yellow_1('#skF_2'))) | ~l1_orders_2(k2_yellow_1('#skF_2')) | ~v2_lattice3(k2_yellow_1('#skF_2')) | ~v5_orders_2(k2_yellow_1('#skF_2')) | v2_struct_0(k2_yellow_1('#skF_2')) | ~m1_subset_1(C_294, '#skF_2') | ~m1_subset_1(B_293, '#skF_2') | ~r1_tarski(B_293, C_294) | ~m1_subset_1(C_294, '#skF_2') | ~m1_subset_1(B_293, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_1611, c_1703])).
% 4.89/1.87  tff(c_1715, plain, (![B_293, C_294]: (r1_orders_2(k2_yellow_1('#skF_2'), k11_lattice3(k2_yellow_1('#skF_2'), B_293, C_294), B_293) | v2_struct_0(k2_yellow_1('#skF_2')) | ~r1_tarski(B_293, C_294) | ~m1_subset_1(C_294, '#skF_2') | ~m1_subset_1(B_293, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_66, c_42, c_52, c_52, c_52, c_1705])).
% 4.89/1.87  tff(c_1723, plain, (v2_struct_0(k2_yellow_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_1715])).
% 4.89/1.87  tff(c_14, plain, (![A_10]: (~v2_struct_0(A_10) | ~v2_lattice3(A_10) | ~l1_orders_2(A_10))), inference(cnfTransformation, [status(thm)], [f_48])).
% 4.89/1.87  tff(c_1726, plain, (~v2_lattice3(k2_yellow_1('#skF_2')) | ~l1_orders_2(k2_yellow_1('#skF_2'))), inference(resolution, [status(thm)], [c_1723, c_14])).
% 4.89/1.87  tff(c_1730, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_66, c_1726])).
% 4.89/1.87  tff(c_1732, plain, (~v2_struct_0(k2_yellow_1('#skF_2'))), inference(splitRight, [status(thm)], [c_1715])).
% 4.89/1.87  tff(c_1408, plain, (![A_255, C_256, B_257]: (k11_lattice3(A_255, C_256, B_257)=k11_lattice3(A_255, B_257, C_256) | ~m1_subset_1(C_256, u1_struct_0(A_255)) | ~m1_subset_1(B_257, u1_struct_0(A_255)) | ~l1_orders_2(A_255) | ~v2_lattice3(A_255) | ~v5_orders_2(A_255))), inference(cnfTransformation, [status(thm)], [f_115])).
% 4.89/1.87  tff(c_1412, plain, (![A_79, C_256, B_257]: (k11_lattice3(k2_yellow_1(A_79), C_256, B_257)=k11_lattice3(k2_yellow_1(A_79), B_257, C_256) | ~m1_subset_1(C_256, A_79) | ~m1_subset_1(B_257, u1_struct_0(k2_yellow_1(A_79))) | ~l1_orders_2(k2_yellow_1(A_79)) | ~v2_lattice3(k2_yellow_1(A_79)) | ~v5_orders_2(k2_yellow_1(A_79)))), inference(superposition, [status(thm), theory('equality')], [c_52, c_1408])).
% 4.89/1.87  tff(c_1421, plain, (![A_261, C_262, B_263]: (k11_lattice3(k2_yellow_1(A_261), C_262, B_263)=k11_lattice3(k2_yellow_1(A_261), B_263, C_262) | ~m1_subset_1(C_262, A_261) | ~m1_subset_1(B_263, A_261) | ~v2_lattice3(k2_yellow_1(A_261)))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_42, c_52, c_1412])).
% 4.89/1.87  tff(c_1424, plain, (![C_262, B_263]: (k11_lattice3(k2_yellow_1('#skF_2'), C_262, B_263)=k11_lattice3(k2_yellow_1('#skF_2'), B_263, C_262) | ~m1_subset_1(C_262, '#skF_2') | ~m1_subset_1(B_263, '#skF_2'))), inference(resolution, [status(thm)], [c_66, c_1421])).
% 4.89/1.87  tff(c_16, plain, (![A_11, B_12, C_13]: (m1_subset_1(k11_lattice3(A_11, B_12, C_13), u1_struct_0(A_11)) | ~m1_subset_1(C_13, u1_struct_0(A_11)) | ~m1_subset_1(B_12, u1_struct_0(A_11)) | ~l1_orders_2(A_11))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.89/1.87  tff(c_1733, plain, (![A_300, B_301, C_302]: (r1_orders_2(A_300, k11_lattice3(A_300, B_301, C_302), C_302) | ~m1_subset_1(k11_lattice3(A_300, B_301, C_302), u1_struct_0(A_300)) | ~m1_subset_1(C_302, u1_struct_0(A_300)) | ~m1_subset_1(B_301, u1_struct_0(A_300)) | ~l1_orders_2(A_300) | ~v2_lattice3(A_300) | ~v5_orders_2(A_300) | v2_struct_0(A_300))), inference(cnfTransformation, [status(thm)], [f_89])).
% 4.89/1.87  tff(c_1842, plain, (![A_323, B_324, C_325]: (r1_orders_2(A_323, k11_lattice3(A_323, B_324, C_325), C_325) | ~v2_lattice3(A_323) | ~v5_orders_2(A_323) | v2_struct_0(A_323) | ~m1_subset_1(C_325, u1_struct_0(A_323)) | ~m1_subset_1(B_324, u1_struct_0(A_323)) | ~l1_orders_2(A_323))), inference(resolution, [status(thm)], [c_16, c_1733])).
% 4.89/1.87  tff(c_1848, plain, (![C_262, B_263]: (r1_orders_2(k2_yellow_1('#skF_2'), k11_lattice3(k2_yellow_1('#skF_2'), C_262, B_263), C_262) | ~v2_lattice3(k2_yellow_1('#skF_2')) | ~v5_orders_2(k2_yellow_1('#skF_2')) | v2_struct_0(k2_yellow_1('#skF_2')) | ~m1_subset_1(C_262, u1_struct_0(k2_yellow_1('#skF_2'))) | ~m1_subset_1(B_263, u1_struct_0(k2_yellow_1('#skF_2'))) | ~l1_orders_2(k2_yellow_1('#skF_2')) | ~m1_subset_1(C_262, '#skF_2') | ~m1_subset_1(B_263, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_1424, c_1842])).
% 4.89/1.87  tff(c_1856, plain, (![C_262, B_263]: (r1_orders_2(k2_yellow_1('#skF_2'), k11_lattice3(k2_yellow_1('#skF_2'), C_262, B_263), C_262) | v2_struct_0(k2_yellow_1('#skF_2')) | ~m1_subset_1(C_262, '#skF_2') | ~m1_subset_1(B_263, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_52, c_52, c_50, c_66, c_1848])).
% 4.89/1.87  tff(c_1857, plain, (![C_262, B_263]: (r1_orders_2(k2_yellow_1('#skF_2'), k11_lattice3(k2_yellow_1('#skF_2'), C_262, B_263), C_262) | ~m1_subset_1(C_262, '#skF_2') | ~m1_subset_1(B_263, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_1732, c_1856])).
% 4.89/1.87  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.89/1.87  tff(c_1845, plain, (![B_293, C_294]: (r1_orders_2(k2_yellow_1('#skF_2'), B_293, C_294) | ~v2_lattice3(k2_yellow_1('#skF_2')) | ~v5_orders_2(k2_yellow_1('#skF_2')) | v2_struct_0(k2_yellow_1('#skF_2')) | ~m1_subset_1(C_294, u1_struct_0(k2_yellow_1('#skF_2'))) | ~m1_subset_1(B_293, u1_struct_0(k2_yellow_1('#skF_2'))) | ~l1_orders_2(k2_yellow_1('#skF_2')) | ~m1_subset_1(C_294, '#skF_2') | ~m1_subset_1(B_293, '#skF_2') | ~r1_tarski(B_293, C_294) | ~m1_subset_1(C_294, '#skF_2') | ~m1_subset_1(B_293, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_1611, c_1842])).
% 4.89/1.87  tff(c_1853, plain, (![B_293, C_294]: (r1_orders_2(k2_yellow_1('#skF_2'), B_293, C_294) | v2_struct_0(k2_yellow_1('#skF_2')) | ~r1_tarski(B_293, C_294) | ~m1_subset_1(C_294, '#skF_2') | ~m1_subset_1(B_293, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_52, c_52, c_50, c_66, c_1845])).
% 4.89/1.87  tff(c_1854, plain, (![B_293, C_294]: (r1_orders_2(k2_yellow_1('#skF_2'), B_293, C_294) | ~r1_tarski(B_293, C_294) | ~m1_subset_1(C_294, '#skF_2') | ~m1_subset_1(B_293, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_1732, c_1853])).
% 4.89/1.87  tff(c_20, plain, (![A_14, B_38, C_50, D_56]: (r1_orders_2(A_14, '#skF_1'(A_14, B_38, C_50, D_56), C_50) | k11_lattice3(A_14, B_38, C_50)=D_56 | ~r1_orders_2(A_14, D_56, C_50) | ~r1_orders_2(A_14, D_56, B_38) | ~m1_subset_1(D_56, u1_struct_0(A_14)) | ~m1_subset_1(C_50, u1_struct_0(A_14)) | ~m1_subset_1(B_38, u1_struct_0(A_14)) | ~l1_orders_2(A_14) | ~v2_lattice3(A_14) | ~v5_orders_2(A_14) | v2_struct_0(A_14))), inference(cnfTransformation, [status(thm)], [f_89])).
% 4.89/1.87  tff(c_2060, plain, (![A_353, B_354, C_355, D_356]: (~r1_orders_2(A_353, '#skF_1'(A_353, B_354, C_355, D_356), D_356) | k11_lattice3(A_353, B_354, C_355)=D_356 | ~r1_orders_2(A_353, D_356, C_355) | ~r1_orders_2(A_353, D_356, B_354) | ~m1_subset_1(D_356, u1_struct_0(A_353)) | ~m1_subset_1(C_355, u1_struct_0(A_353)) | ~m1_subset_1(B_354, u1_struct_0(A_353)) | ~l1_orders_2(A_353) | ~v2_lattice3(A_353) | ~v5_orders_2(A_353) | v2_struct_0(A_353))), inference(cnfTransformation, [status(thm)], [f_89])).
% 4.89/1.87  tff(c_2079, plain, (![A_357, B_358, C_359]: (k11_lattice3(A_357, B_358, C_359)=C_359 | ~r1_orders_2(A_357, C_359, C_359) | ~r1_orders_2(A_357, C_359, B_358) | ~m1_subset_1(C_359, u1_struct_0(A_357)) | ~m1_subset_1(B_358, u1_struct_0(A_357)) | ~l1_orders_2(A_357) | ~v2_lattice3(A_357) | ~v5_orders_2(A_357) | v2_struct_0(A_357))), inference(resolution, [status(thm)], [c_20, c_2060])).
% 4.89/1.87  tff(c_2082, plain, (![B_358, C_294]: (k11_lattice3(k2_yellow_1('#skF_2'), B_358, C_294)=C_294 | ~r1_orders_2(k2_yellow_1('#skF_2'), C_294, B_358) | ~m1_subset_1(C_294, u1_struct_0(k2_yellow_1('#skF_2'))) | ~m1_subset_1(B_358, u1_struct_0(k2_yellow_1('#skF_2'))) | ~l1_orders_2(k2_yellow_1('#skF_2')) | ~v2_lattice3(k2_yellow_1('#skF_2')) | ~v5_orders_2(k2_yellow_1('#skF_2')) | v2_struct_0(k2_yellow_1('#skF_2')) | ~r1_tarski(C_294, C_294) | ~m1_subset_1(C_294, '#skF_2'))), inference(resolution, [status(thm)], [c_1854, c_2079])).
% 4.89/1.87  tff(c_2087, plain, (![B_358, C_294]: (k11_lattice3(k2_yellow_1('#skF_2'), B_358, C_294)=C_294 | ~r1_orders_2(k2_yellow_1('#skF_2'), C_294, B_358) | ~m1_subset_1(B_358, '#skF_2') | v2_struct_0(k2_yellow_1('#skF_2')) | ~m1_subset_1(C_294, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_50, c_66, c_42, c_52, c_52, c_2082])).
% 4.89/1.87  tff(c_2093, plain, (![B_360, C_361]: (k11_lattice3(k2_yellow_1('#skF_2'), B_360, C_361)=C_361 | ~r1_orders_2(k2_yellow_1('#skF_2'), C_361, B_360) | ~m1_subset_1(B_360, '#skF_2') | ~m1_subset_1(C_361, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_1732, c_2087])).
% 4.89/1.87  tff(c_2370, plain, (![C_365, B_366]: (k11_lattice3(k2_yellow_1('#skF_2'), C_365, k11_lattice3(k2_yellow_1('#skF_2'), C_365, B_366))=k11_lattice3(k2_yellow_1('#skF_2'), C_365, B_366) | ~m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'), C_365, B_366), '#skF_2') | ~m1_subset_1(C_365, '#skF_2') | ~m1_subset_1(B_366, '#skF_2'))), inference(resolution, [status(thm)], [c_1857, c_2093])).
% 4.89/1.87  tff(c_1549, plain, (![A_274, B_275, C_276]: (r3_orders_2(A_274, B_275, C_276) | k12_lattice3(A_274, B_275, C_276)!=B_275 | ~m1_subset_1(C_276, u1_struct_0(A_274)) | ~m1_subset_1(B_275, u1_struct_0(A_274)) | ~l1_orders_2(A_274) | ~v2_lattice3(A_274) | ~v5_orders_2(A_274) | ~v3_orders_2(A_274))), inference(cnfTransformation, [status(thm)], [f_133])).
% 4.89/1.87  tff(c_1556, plain, (![A_79, B_275, C_276]: (r3_orders_2(k2_yellow_1(A_79), B_275, C_276) | k12_lattice3(k2_yellow_1(A_79), B_275, C_276)!=B_275 | ~m1_subset_1(C_276, A_79) | ~m1_subset_1(B_275, u1_struct_0(k2_yellow_1(A_79))) | ~l1_orders_2(k2_yellow_1(A_79)) | ~v2_lattice3(k2_yellow_1(A_79)) | ~v5_orders_2(k2_yellow_1(A_79)) | ~v3_orders_2(k2_yellow_1(A_79)))), inference(superposition, [status(thm), theory('equality')], [c_52, c_1549])).
% 4.89/1.87  tff(c_1561, plain, (![A_277, B_278, C_279]: (r3_orders_2(k2_yellow_1(A_277), B_278, C_279) | k12_lattice3(k2_yellow_1(A_277), B_278, C_279)!=B_278 | ~m1_subset_1(C_279, A_277) | ~m1_subset_1(B_278, A_277) | ~v2_lattice3(k2_yellow_1(A_277)))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_50, c_42, c_52, c_1556])).
% 4.89/1.87  tff(c_58, plain, (![B_84, C_86, A_80]: (r1_tarski(B_84, C_86) | ~r3_orders_2(k2_yellow_1(A_80), B_84, C_86) | ~m1_subset_1(C_86, u1_struct_0(k2_yellow_1(A_80))) | ~m1_subset_1(B_84, u1_struct_0(k2_yellow_1(A_80))) | v1_xboole_0(A_80))), inference(cnfTransformation, [status(thm)], [f_162])).
% 4.89/1.87  tff(c_71, plain, (![B_84, C_86, A_80]: (r1_tarski(B_84, C_86) | ~r3_orders_2(k2_yellow_1(A_80), B_84, C_86) | ~m1_subset_1(C_86, A_80) | ~m1_subset_1(B_84, A_80) | v1_xboole_0(A_80))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_52, c_58])).
% 4.89/1.87  tff(c_1566, plain, (![B_280, C_281, A_282]: (r1_tarski(B_280, C_281) | v1_xboole_0(A_282) | k12_lattice3(k2_yellow_1(A_282), B_280, C_281)!=B_280 | ~m1_subset_1(C_281, A_282) | ~m1_subset_1(B_280, A_282) | ~v2_lattice3(k2_yellow_1(A_282)))), inference(resolution, [status(thm)], [c_1561, c_71])).
% 4.89/1.87  tff(c_1568, plain, (![B_270, C_271]: (r1_tarski(B_270, C_271) | v1_xboole_0('#skF_2') | k11_lattice3(k2_yellow_1('#skF_2'), B_270, C_271)!=B_270 | ~m1_subset_1(C_271, '#skF_2') | ~m1_subset_1(B_270, '#skF_2') | ~v2_lattice3(k2_yellow_1('#skF_2')) | ~m1_subset_1(C_271, '#skF_2') | ~m1_subset_1(B_270, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_1539, c_1566])).
% 4.89/1.87  tff(c_1570, plain, (![B_270, C_271]: (r1_tarski(B_270, C_271) | v1_xboole_0('#skF_2') | k11_lattice3(k2_yellow_1('#skF_2'), B_270, C_271)!=B_270 | ~m1_subset_1(C_271, '#skF_2') | ~m1_subset_1(B_270, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_1568])).
% 4.89/1.87  tff(c_1572, plain, (![B_283, C_284]: (r1_tarski(B_283, C_284) | k11_lattice3(k2_yellow_1('#skF_2'), B_283, C_284)!=B_283 | ~m1_subset_1(C_284, '#skF_2') | ~m1_subset_1(B_283, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_68, c_1570])).
% 4.89/1.87  tff(c_1575, plain, (![B_263, C_262]: (r1_tarski(B_263, C_262) | k11_lattice3(k2_yellow_1('#skF_2'), C_262, B_263)!=B_263 | ~m1_subset_1(C_262, '#skF_2') | ~m1_subset_1(B_263, '#skF_2') | ~m1_subset_1(C_262, '#skF_2') | ~m1_subset_1(B_263, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_1424, c_1572])).
% 4.89/1.87  tff(c_2464, plain, (![C_367, B_368]: (r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'), C_367, B_368), C_367) | ~m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'), C_367, B_368), '#skF_2') | ~m1_subset_1(C_367, '#skF_2') | ~m1_subset_1(B_368, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_2370, c_1575])).
% 4.89/1.87  tff(c_1425, plain, (![C_264, B_265]: (k11_lattice3(k2_yellow_1('#skF_2'), C_264, B_265)=k11_lattice3(k2_yellow_1('#skF_2'), B_265, C_264) | ~m1_subset_1(C_264, '#skF_2') | ~m1_subset_1(B_265, '#skF_2'))), inference(resolution, [status(thm)], [c_66, c_1421])).
% 4.89/1.87  tff(c_152, plain, (![A_118, B_119, C_120]: (m1_subset_1(k11_lattice3(A_118, B_119, C_120), u1_struct_0(A_118)) | ~m1_subset_1(C_120, u1_struct_0(A_118)) | ~m1_subset_1(B_119, u1_struct_0(A_118)) | ~l1_orders_2(A_118))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.89/1.87  tff(c_155, plain, (![A_79, B_119, C_120]: (m1_subset_1(k11_lattice3(k2_yellow_1(A_79), B_119, C_120), A_79) | ~m1_subset_1(C_120, u1_struct_0(k2_yellow_1(A_79))) | ~m1_subset_1(B_119, u1_struct_0(k2_yellow_1(A_79))) | ~l1_orders_2(k2_yellow_1(A_79)))), inference(superposition, [status(thm), theory('equality')], [c_52, c_152])).
% 4.89/1.87  tff(c_157, plain, (![A_79, B_119, C_120]: (m1_subset_1(k11_lattice3(k2_yellow_1(A_79), B_119, C_120), A_79) | ~m1_subset_1(C_120, A_79) | ~m1_subset_1(B_119, A_79))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_52, c_52, c_155])).
% 4.89/1.87  tff(c_273, plain, (![A_140, B_141, C_142]: (k12_lattice3(A_140, B_141, C_142)=B_141 | ~r3_orders_2(A_140, B_141, C_142) | ~m1_subset_1(C_142, u1_struct_0(A_140)) | ~m1_subset_1(B_141, u1_struct_0(A_140)) | ~l1_orders_2(A_140) | ~v2_lattice3(A_140) | ~v5_orders_2(A_140) | ~v3_orders_2(A_140))), inference(cnfTransformation, [status(thm)], [f_133])).
% 4.89/1.87  tff(c_275, plain, (![A_80, B_84, C_86]: (k12_lattice3(k2_yellow_1(A_80), B_84, C_86)=B_84 | ~m1_subset_1(C_86, u1_struct_0(k2_yellow_1(A_80))) | ~m1_subset_1(B_84, u1_struct_0(k2_yellow_1(A_80))) | ~l1_orders_2(k2_yellow_1(A_80)) | ~v2_lattice3(k2_yellow_1(A_80)) | ~v5_orders_2(k2_yellow_1(A_80)) | ~v3_orders_2(k2_yellow_1(A_80)) | ~r1_tarski(B_84, C_86) | ~m1_subset_1(C_86, A_80) | ~m1_subset_1(B_84, A_80) | v1_xboole_0(A_80))), inference(resolution, [status(thm)], [c_72, c_273])).
% 4.89/1.87  tff(c_279, plain, (![A_143, B_144, C_145]: (k12_lattice3(k2_yellow_1(A_143), B_144, C_145)=B_144 | ~v2_lattice3(k2_yellow_1(A_143)) | ~r1_tarski(B_144, C_145) | ~m1_subset_1(C_145, A_143) | ~m1_subset_1(B_144, A_143) | v1_xboole_0(A_143))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_50, c_42, c_52, c_52, c_275])).
% 4.89/1.87  tff(c_281, plain, (![B_144, C_145]: (k12_lattice3(k2_yellow_1('#skF_2'), B_144, C_145)=B_144 | ~r1_tarski(B_144, C_145) | ~m1_subset_1(C_145, '#skF_2') | ~m1_subset_1(B_144, '#skF_2') | v1_xboole_0('#skF_2'))), inference(resolution, [status(thm)], [c_66, c_279])).
% 4.89/1.87  tff(c_285, plain, (![B_146, C_147]: (k12_lattice3(k2_yellow_1('#skF_2'), B_146, C_147)=B_146 | ~r1_tarski(B_146, C_147) | ~m1_subset_1(C_147, '#skF_2') | ~m1_subset_1(B_146, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_68, c_281])).
% 4.89/1.87  tff(c_248, plain, (![A_132, B_133, C_134]: (k12_lattice3(A_132, B_133, C_134)=k11_lattice3(A_132, B_133, C_134) | ~m1_subset_1(C_134, u1_struct_0(A_132)) | ~m1_subset_1(B_133, u1_struct_0(A_132)) | ~l1_orders_2(A_132) | ~v2_lattice3(A_132) | ~v5_orders_2(A_132))), inference(cnfTransformation, [status(thm)], [f_101])).
% 4.89/1.87  tff(c_255, plain, (![A_79, B_133, C_134]: (k12_lattice3(k2_yellow_1(A_79), B_133, C_134)=k11_lattice3(k2_yellow_1(A_79), B_133, C_134) | ~m1_subset_1(C_134, A_79) | ~m1_subset_1(B_133, u1_struct_0(k2_yellow_1(A_79))) | ~l1_orders_2(k2_yellow_1(A_79)) | ~v2_lattice3(k2_yellow_1(A_79)) | ~v5_orders_2(k2_yellow_1(A_79)))), inference(superposition, [status(thm), theory('equality')], [c_52, c_248])).
% 4.89/1.87  tff(c_260, plain, (![A_135, B_136, C_137]: (k12_lattice3(k2_yellow_1(A_135), B_136, C_137)=k11_lattice3(k2_yellow_1(A_135), B_136, C_137) | ~m1_subset_1(C_137, A_135) | ~m1_subset_1(B_136, A_135) | ~v2_lattice3(k2_yellow_1(A_135)))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_42, c_52, c_255])).
% 4.89/1.87  tff(c_263, plain, (![B_136, C_137]: (k12_lattice3(k2_yellow_1('#skF_2'), B_136, C_137)=k11_lattice3(k2_yellow_1('#skF_2'), B_136, C_137) | ~m1_subset_1(C_137, '#skF_2') | ~m1_subset_1(B_136, '#skF_2'))), inference(resolution, [status(thm)], [c_66, c_260])).
% 4.89/1.87  tff(c_291, plain, (![B_146, C_147]: (k11_lattice3(k2_yellow_1('#skF_2'), B_146, C_147)=B_146 | ~m1_subset_1(C_147, '#skF_2') | ~m1_subset_1(B_146, '#skF_2') | ~r1_tarski(B_146, C_147) | ~m1_subset_1(C_147, '#skF_2') | ~m1_subset_1(B_146, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_285, c_263])).
% 4.89/1.87  tff(c_487, plain, (![A_172, B_173, C_174]: (r1_orders_2(A_172, k11_lattice3(A_172, B_173, C_174), B_173) | ~m1_subset_1(k11_lattice3(A_172, B_173, C_174), u1_struct_0(A_172)) | ~m1_subset_1(C_174, u1_struct_0(A_172)) | ~m1_subset_1(B_173, u1_struct_0(A_172)) | ~l1_orders_2(A_172) | ~v2_lattice3(A_172) | ~v5_orders_2(A_172) | v2_struct_0(A_172))), inference(cnfTransformation, [status(thm)], [f_89])).
% 4.89/1.87  tff(c_491, plain, (![B_146, C_147]: (r1_orders_2(k2_yellow_1('#skF_2'), k11_lattice3(k2_yellow_1('#skF_2'), B_146, C_147), B_146) | ~m1_subset_1(B_146, u1_struct_0(k2_yellow_1('#skF_2'))) | ~m1_subset_1(C_147, u1_struct_0(k2_yellow_1('#skF_2'))) | ~m1_subset_1(B_146, u1_struct_0(k2_yellow_1('#skF_2'))) | ~l1_orders_2(k2_yellow_1('#skF_2')) | ~v2_lattice3(k2_yellow_1('#skF_2')) | ~v5_orders_2(k2_yellow_1('#skF_2')) | v2_struct_0(k2_yellow_1('#skF_2')) | ~m1_subset_1(C_147, '#skF_2') | ~m1_subset_1(B_146, '#skF_2') | ~r1_tarski(B_146, C_147) | ~m1_subset_1(C_147, '#skF_2') | ~m1_subset_1(B_146, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_291, c_487])).
% 4.89/1.87  tff(c_503, plain, (![B_146, C_147]: (r1_orders_2(k2_yellow_1('#skF_2'), k11_lattice3(k2_yellow_1('#skF_2'), B_146, C_147), B_146) | v2_struct_0(k2_yellow_1('#skF_2')) | ~r1_tarski(B_146, C_147) | ~m1_subset_1(C_147, '#skF_2') | ~m1_subset_1(B_146, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_66, c_42, c_52, c_52, c_52, c_491])).
% 4.89/1.87  tff(c_511, plain, (v2_struct_0(k2_yellow_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_503])).
% 4.89/1.87  tff(c_514, plain, (~v2_lattice3(k2_yellow_1('#skF_2')) | ~l1_orders_2(k2_yellow_1('#skF_2'))), inference(resolution, [status(thm)], [c_511, c_14])).
% 4.89/1.87  tff(c_518, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_66, c_514])).
% 4.89/1.87  tff(c_520, plain, (~v2_struct_0(k2_yellow_1('#skF_2'))), inference(splitRight, [status(thm)], [c_503])).
% 4.89/1.87  tff(c_159, plain, (![A_124, C_125, B_126]: (k11_lattice3(A_124, C_125, B_126)=k11_lattice3(A_124, B_126, C_125) | ~m1_subset_1(C_125, u1_struct_0(A_124)) | ~m1_subset_1(B_126, u1_struct_0(A_124)) | ~l1_orders_2(A_124) | ~v2_lattice3(A_124) | ~v5_orders_2(A_124))), inference(cnfTransformation, [status(thm)], [f_115])).
% 4.89/1.87  tff(c_166, plain, (![A_79, C_125, B_126]: (k11_lattice3(k2_yellow_1(A_79), C_125, B_126)=k11_lattice3(k2_yellow_1(A_79), B_126, C_125) | ~m1_subset_1(C_125, A_79) | ~m1_subset_1(B_126, u1_struct_0(k2_yellow_1(A_79))) | ~l1_orders_2(k2_yellow_1(A_79)) | ~v2_lattice3(k2_yellow_1(A_79)) | ~v5_orders_2(k2_yellow_1(A_79)))), inference(superposition, [status(thm), theory('equality')], [c_52, c_159])).
% 4.89/1.87  tff(c_171, plain, (![A_127, C_128, B_129]: (k11_lattice3(k2_yellow_1(A_127), C_128, B_129)=k11_lattice3(k2_yellow_1(A_127), B_129, C_128) | ~m1_subset_1(C_128, A_127) | ~m1_subset_1(B_129, A_127) | ~v2_lattice3(k2_yellow_1(A_127)))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_42, c_52, c_166])).
% 4.89/1.87  tff(c_174, plain, (![C_128, B_129]: (k11_lattice3(k2_yellow_1('#skF_2'), C_128, B_129)=k11_lattice3(k2_yellow_1('#skF_2'), B_129, C_128) | ~m1_subset_1(C_128, '#skF_2') | ~m1_subset_1(B_129, '#skF_2'))), inference(resolution, [status(thm)], [c_66, c_171])).
% 4.89/1.87  tff(c_548, plain, (![A_179, B_180, C_181]: (r1_orders_2(A_179, k11_lattice3(A_179, B_180, C_181), B_180) | ~v2_lattice3(A_179) | ~v5_orders_2(A_179) | v2_struct_0(A_179) | ~m1_subset_1(C_181, u1_struct_0(A_179)) | ~m1_subset_1(B_180, u1_struct_0(A_179)) | ~l1_orders_2(A_179))), inference(resolution, [status(thm)], [c_16, c_487])).
% 4.89/1.87  tff(c_557, plain, (![C_128, B_129]: (r1_orders_2(k2_yellow_1('#skF_2'), k11_lattice3(k2_yellow_1('#skF_2'), C_128, B_129), B_129) | ~v2_lattice3(k2_yellow_1('#skF_2')) | ~v5_orders_2(k2_yellow_1('#skF_2')) | v2_struct_0(k2_yellow_1('#skF_2')) | ~m1_subset_1(C_128, u1_struct_0(k2_yellow_1('#skF_2'))) | ~m1_subset_1(B_129, u1_struct_0(k2_yellow_1('#skF_2'))) | ~l1_orders_2(k2_yellow_1('#skF_2')) | ~m1_subset_1(C_128, '#skF_2') | ~m1_subset_1(B_129, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_174, c_548])).
% 4.89/1.87  tff(c_568, plain, (![C_128, B_129]: (r1_orders_2(k2_yellow_1('#skF_2'), k11_lattice3(k2_yellow_1('#skF_2'), C_128, B_129), B_129) | v2_struct_0(k2_yellow_1('#skF_2')) | ~m1_subset_1(C_128, '#skF_2') | ~m1_subset_1(B_129, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_52, c_52, c_50, c_66, c_557])).
% 4.89/1.87  tff(c_569, plain, (![C_128, B_129]: (r1_orders_2(k2_yellow_1('#skF_2'), k11_lattice3(k2_yellow_1('#skF_2'), C_128, B_129), B_129) | ~m1_subset_1(C_128, '#skF_2') | ~m1_subset_1(B_129, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_520, c_568])).
% 4.89/1.87  tff(c_300, plain, (![B_148, C_149]: (k11_lattice3(k2_yellow_1('#skF_2'), B_148, C_149)=B_148 | ~m1_subset_1(C_149, '#skF_2') | ~m1_subset_1(B_148, '#skF_2') | ~r1_tarski(B_148, C_149) | ~m1_subset_1(C_149, '#skF_2') | ~m1_subset_1(B_148, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_285, c_263])).
% 4.89/1.87  tff(c_315, plain, (![C_149, B_148]: (k11_lattice3(k2_yellow_1('#skF_2'), C_149, B_148)=B_148 | ~m1_subset_1(C_149, '#skF_2') | ~m1_subset_1(B_148, '#skF_2') | ~m1_subset_1(C_149, '#skF_2') | ~m1_subset_1(B_148, '#skF_2') | ~r1_tarski(B_148, C_149) | ~m1_subset_1(C_149, '#skF_2') | ~m1_subset_1(B_148, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_300, c_174])).
% 4.89/1.87  tff(c_551, plain, (![B_148, C_149]: (r1_orders_2(k2_yellow_1('#skF_2'), B_148, C_149) | ~v2_lattice3(k2_yellow_1('#skF_2')) | ~v5_orders_2(k2_yellow_1('#skF_2')) | v2_struct_0(k2_yellow_1('#skF_2')) | ~m1_subset_1(B_148, u1_struct_0(k2_yellow_1('#skF_2'))) | ~m1_subset_1(C_149, u1_struct_0(k2_yellow_1('#skF_2'))) | ~l1_orders_2(k2_yellow_1('#skF_2')) | ~m1_subset_1(C_149, '#skF_2') | ~m1_subset_1(B_148, '#skF_2') | ~m1_subset_1(C_149, '#skF_2') | ~m1_subset_1(B_148, '#skF_2') | ~r1_tarski(B_148, C_149) | ~m1_subset_1(C_149, '#skF_2') | ~m1_subset_1(B_148, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_315, c_548])).
% 4.89/1.87  tff(c_562, plain, (![B_148, C_149]: (r1_orders_2(k2_yellow_1('#skF_2'), B_148, C_149) | v2_struct_0(k2_yellow_1('#skF_2')) | ~r1_tarski(B_148, C_149) | ~m1_subset_1(C_149, '#skF_2') | ~m1_subset_1(B_148, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_52, c_52, c_50, c_66, c_551])).
% 4.89/1.87  tff(c_563, plain, (![B_148, C_149]: (r1_orders_2(k2_yellow_1('#skF_2'), B_148, C_149) | ~r1_tarski(B_148, C_149) | ~m1_subset_1(C_149, '#skF_2') | ~m1_subset_1(B_148, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_520, c_562])).
% 4.89/1.87  tff(c_880, plain, (![A_218, B_219, C_220, D_221]: (r1_orders_2(A_218, '#skF_1'(A_218, B_219, C_220, D_221), C_220) | k11_lattice3(A_218, B_219, C_220)=D_221 | ~r1_orders_2(A_218, D_221, C_220) | ~r1_orders_2(A_218, D_221, B_219) | ~m1_subset_1(D_221, u1_struct_0(A_218)) | ~m1_subset_1(C_220, u1_struct_0(A_218)) | ~m1_subset_1(B_219, u1_struct_0(A_218)) | ~l1_orders_2(A_218) | ~v2_lattice3(A_218) | ~v5_orders_2(A_218) | v2_struct_0(A_218))), inference(cnfTransformation, [status(thm)], [f_89])).
% 4.89/1.87  tff(c_18, plain, (![A_14, B_38, C_50, D_56]: (~r1_orders_2(A_14, '#skF_1'(A_14, B_38, C_50, D_56), D_56) | k11_lattice3(A_14, B_38, C_50)=D_56 | ~r1_orders_2(A_14, D_56, C_50) | ~r1_orders_2(A_14, D_56, B_38) | ~m1_subset_1(D_56, u1_struct_0(A_14)) | ~m1_subset_1(C_50, u1_struct_0(A_14)) | ~m1_subset_1(B_38, u1_struct_0(A_14)) | ~l1_orders_2(A_14) | ~v2_lattice3(A_14) | ~v5_orders_2(A_14) | v2_struct_0(A_14))), inference(cnfTransformation, [status(thm)], [f_89])).
% 4.89/1.87  tff(c_1115, plain, (![A_228, B_229, C_230]: (k11_lattice3(A_228, B_229, C_230)=C_230 | ~r1_orders_2(A_228, C_230, C_230) | ~r1_orders_2(A_228, C_230, B_229) | ~m1_subset_1(C_230, u1_struct_0(A_228)) | ~m1_subset_1(B_229, u1_struct_0(A_228)) | ~l1_orders_2(A_228) | ~v2_lattice3(A_228) | ~v5_orders_2(A_228) | v2_struct_0(A_228))), inference(resolution, [status(thm)], [c_880, c_18])).
% 4.89/1.87  tff(c_1118, plain, (![B_229, C_149]: (k11_lattice3(k2_yellow_1('#skF_2'), B_229, C_149)=C_149 | ~r1_orders_2(k2_yellow_1('#skF_2'), C_149, B_229) | ~m1_subset_1(C_149, u1_struct_0(k2_yellow_1('#skF_2'))) | ~m1_subset_1(B_229, u1_struct_0(k2_yellow_1('#skF_2'))) | ~l1_orders_2(k2_yellow_1('#skF_2')) | ~v2_lattice3(k2_yellow_1('#skF_2')) | ~v5_orders_2(k2_yellow_1('#skF_2')) | v2_struct_0(k2_yellow_1('#skF_2')) | ~r1_tarski(C_149, C_149) | ~m1_subset_1(C_149, '#skF_2'))), inference(resolution, [status(thm)], [c_563, c_1115])).
% 4.89/1.87  tff(c_1123, plain, (![B_229, C_149]: (k11_lattice3(k2_yellow_1('#skF_2'), B_229, C_149)=C_149 | ~r1_orders_2(k2_yellow_1('#skF_2'), C_149, B_229) | ~m1_subset_1(B_229, '#skF_2') | v2_struct_0(k2_yellow_1('#skF_2')) | ~m1_subset_1(C_149, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_50, c_66, c_42, c_52, c_52, c_1118])).
% 4.89/1.87  tff(c_1129, plain, (![B_231, C_232]: (k11_lattice3(k2_yellow_1('#skF_2'), B_231, C_232)=C_232 | ~r1_orders_2(k2_yellow_1('#skF_2'), C_232, B_231) | ~m1_subset_1(B_231, '#skF_2') | ~m1_subset_1(C_232, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_520, c_1123])).
% 4.89/1.87  tff(c_1209, plain, (![B_237, C_238]: (k11_lattice3(k2_yellow_1('#skF_2'), B_237, k11_lattice3(k2_yellow_1('#skF_2'), C_238, B_237))=k11_lattice3(k2_yellow_1('#skF_2'), C_238, B_237) | ~m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'), C_238, B_237), '#skF_2') | ~m1_subset_1(C_238, '#skF_2') | ~m1_subset_1(B_237, '#skF_2'))), inference(resolution, [status(thm)], [c_569, c_1129])).
% 4.89/1.87  tff(c_350, plain, (![A_150, B_151, C_152]: (r3_orders_2(A_150, B_151, C_152) | k12_lattice3(A_150, B_151, C_152)!=B_151 | ~m1_subset_1(C_152, u1_struct_0(A_150)) | ~m1_subset_1(B_151, u1_struct_0(A_150)) | ~l1_orders_2(A_150) | ~v2_lattice3(A_150) | ~v5_orders_2(A_150) | ~v3_orders_2(A_150))), inference(cnfTransformation, [status(thm)], [f_133])).
% 4.89/1.87  tff(c_357, plain, (![A_79, B_151, C_152]: (r3_orders_2(k2_yellow_1(A_79), B_151, C_152) | k12_lattice3(k2_yellow_1(A_79), B_151, C_152)!=B_151 | ~m1_subset_1(C_152, A_79) | ~m1_subset_1(B_151, u1_struct_0(k2_yellow_1(A_79))) | ~l1_orders_2(k2_yellow_1(A_79)) | ~v2_lattice3(k2_yellow_1(A_79)) | ~v5_orders_2(k2_yellow_1(A_79)) | ~v3_orders_2(k2_yellow_1(A_79)))), inference(superposition, [status(thm), theory('equality')], [c_52, c_350])).
% 4.89/1.87  tff(c_362, plain, (![A_153, B_154, C_155]: (r3_orders_2(k2_yellow_1(A_153), B_154, C_155) | k12_lattice3(k2_yellow_1(A_153), B_154, C_155)!=B_154 | ~m1_subset_1(C_155, A_153) | ~m1_subset_1(B_154, A_153) | ~v2_lattice3(k2_yellow_1(A_153)))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_50, c_42, c_52, c_357])).
% 4.89/1.87  tff(c_372, plain, (![B_156, C_157, A_158]: (r1_tarski(B_156, C_157) | v1_xboole_0(A_158) | k12_lattice3(k2_yellow_1(A_158), B_156, C_157)!=B_156 | ~m1_subset_1(C_157, A_158) | ~m1_subset_1(B_156, A_158) | ~v2_lattice3(k2_yellow_1(A_158)))), inference(resolution, [status(thm)], [c_362, c_71])).
% 4.89/1.87  tff(c_376, plain, (![B_136, C_137]: (r1_tarski(B_136, C_137) | v1_xboole_0('#skF_2') | k11_lattice3(k2_yellow_1('#skF_2'), B_136, C_137)!=B_136 | ~m1_subset_1(C_137, '#skF_2') | ~m1_subset_1(B_136, '#skF_2') | ~v2_lattice3(k2_yellow_1('#skF_2')) | ~m1_subset_1(C_137, '#skF_2') | ~m1_subset_1(B_136, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_263, c_372])).
% 4.89/1.87  tff(c_382, plain, (![B_136, C_137]: (r1_tarski(B_136, C_137) | v1_xboole_0('#skF_2') | k11_lattice3(k2_yellow_1('#skF_2'), B_136, C_137)!=B_136 | ~m1_subset_1(C_137, '#skF_2') | ~m1_subset_1(B_136, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_376])).
% 4.89/1.87  tff(c_384, plain, (![B_159, C_160]: (r1_tarski(B_159, C_160) | k11_lattice3(k2_yellow_1('#skF_2'), B_159, C_160)!=B_159 | ~m1_subset_1(C_160, '#skF_2') | ~m1_subset_1(B_159, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_68, c_382])).
% 4.89/1.87  tff(c_390, plain, (![B_129, C_128]: (r1_tarski(B_129, C_128) | k11_lattice3(k2_yellow_1('#skF_2'), C_128, B_129)!=B_129 | ~m1_subset_1(C_128, '#skF_2') | ~m1_subset_1(B_129, '#skF_2') | ~m1_subset_1(C_128, '#skF_2') | ~m1_subset_1(B_129, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_174, c_384])).
% 4.89/1.87  tff(c_1300, plain, (![C_239, B_240]: (r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'), C_239, B_240), B_240) | ~m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'), C_239, B_240), '#skF_2') | ~m1_subset_1(C_239, '#skF_2') | ~m1_subset_1(B_240, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_1209, c_390])).
% 4.89/1.87  tff(c_175, plain, (![C_130, B_131]: (k11_lattice3(k2_yellow_1('#skF_2'), C_130, B_131)=k11_lattice3(k2_yellow_1('#skF_2'), B_131, C_130) | ~m1_subset_1(C_130, '#skF_2') | ~m1_subset_1(B_131, '#skF_2'))), inference(resolution, [status(thm)], [c_66, c_171])).
% 4.89/1.87  tff(c_125, plain, (![A_106, B_107, C_108]: (r1_tarski(A_106, k3_xboole_0(B_107, C_108)) | ~r1_tarski(A_106, C_108) | ~r1_tarski(A_106, B_107))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.89/1.87  tff(c_60, plain, (~r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4'), k3_xboole_0('#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_176])).
% 4.89/1.87  tff(c_132, plain, (~r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4'), '#skF_4') | ~r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4'), '#skF_3')), inference(resolution, [status(thm)], [c_125, c_60])).
% 4.89/1.87  tff(c_133, plain, (~r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4'), '#skF_3')), inference(splitLeft, [status(thm)], [c_132])).
% 4.89/1.87  tff(c_202, plain, (~r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'), '#skF_4', '#skF_3'), '#skF_3') | ~m1_subset_1('#skF_4', '#skF_2') | ~m1_subset_1('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_175, c_133])).
% 4.89/1.87  tff(c_233, plain, (~r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'), '#skF_4', '#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_69, c_70, c_202])).
% 4.89/1.87  tff(c_1303, plain, (~m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'), '#skF_4', '#skF_3'), '#skF_2') | ~m1_subset_1('#skF_4', '#skF_2') | ~m1_subset_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_1300, c_233])).
% 4.89/1.87  tff(c_1326, plain, (~m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'), '#skF_4', '#skF_3'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_69, c_70, c_1303])).
% 4.89/1.87  tff(c_1369, plain, (~m1_subset_1('#skF_3', '#skF_2') | ~m1_subset_1('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_157, c_1326])).
% 4.89/1.87  tff(c_1377, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_70, c_69, c_1369])).
% 4.89/1.87  tff(c_1378, plain, (~r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4'), '#skF_4')), inference(splitRight, [status(thm)], [c_132])).
% 4.89/1.87  tff(c_1464, plain, (~r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'), '#skF_4', '#skF_3'), '#skF_4') | ~m1_subset_1('#skF_4', '#skF_2') | ~m1_subset_1('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1425, c_1378])).
% 4.89/1.87  tff(c_1503, plain, (~r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'), '#skF_4', '#skF_3'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_69, c_70, c_1464])).
% 4.89/1.87  tff(c_2467, plain, (~m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'), '#skF_4', '#skF_3'), '#skF_2') | ~m1_subset_1('#skF_4', '#skF_2') | ~m1_subset_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_2464, c_1503])).
% 4.89/1.87  tff(c_2490, plain, (~m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'), '#skF_4', '#skF_3'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_69, c_70, c_2467])).
% 4.89/1.87  tff(c_2502, plain, (~m1_subset_1('#skF_3', '#skF_2') | ~m1_subset_1('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_1407, c_2490])).
% 4.89/1.87  tff(c_2510, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_70, c_69, c_2502])).
% 4.89/1.87  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.89/1.87  
% 4.89/1.87  Inference rules
% 4.89/1.87  ----------------------
% 4.89/1.87  #Ref     : 0
% 4.89/1.87  #Sup     : 525
% 4.89/1.87  #Fact    : 0
% 4.89/1.87  #Define  : 0
% 4.89/1.87  #Split   : 5
% 4.89/1.87  #Chain   : 0
% 4.89/1.87  #Close   : 0
% 4.89/1.87  
% 4.89/1.87  Ordering : KBO
% 4.89/1.87  
% 4.89/1.87  Simplification rules
% 4.89/1.87  ----------------------
% 4.89/1.87  #Subsume      : 246
% 4.89/1.87  #Demod        : 790
% 4.89/1.87  #Tautology    : 135
% 4.89/1.87  #SimpNegUnit  : 102
% 4.89/1.87  #BackRed      : 0
% 4.89/1.87  
% 4.89/1.87  #Partial instantiations: 0
% 4.89/1.87  #Strategies tried      : 1
% 4.89/1.87  
% 4.89/1.87  Timing (in seconds)
% 4.89/1.87  ----------------------
% 4.89/1.87  Preprocessing        : 0.36
% 4.89/1.87  Parsing              : 0.18
% 4.89/1.87  CNF conversion       : 0.03
% 4.89/1.87  Main loop            : 0.71
% 4.89/1.87  Inferencing          : 0.26
% 4.89/1.87  Reduction            : 0.24
% 4.89/1.87  Demodulation         : 0.17
% 4.89/1.87  BG Simplification    : 0.04
% 4.89/1.87  Subsumption          : 0.13
% 4.89/1.87  Abstraction          : 0.04
% 4.89/1.87  MUC search           : 0.00
% 4.89/1.87  Cooper               : 0.00
% 4.89/1.87  Total                : 1.13
% 4.89/1.87  Index Insertion      : 0.00
% 4.89/1.87  Index Deletion       : 0.00
% 4.89/1.87  Index Matching       : 0.00
% 4.89/1.87  BG Taut test         : 0.00
%------------------------------------------------------------------------------
