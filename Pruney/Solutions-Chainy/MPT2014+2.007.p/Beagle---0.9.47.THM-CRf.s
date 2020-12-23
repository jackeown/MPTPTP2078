%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:31:09 EST 2020

% Result     : Theorem 3.10s
% Output     : CNFRefutation 3.35s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 147 expanded)
%              Number of leaves         :   36 (  68 expanded)
%              Depth                    :   15
%              Number of atoms          :  207 ( 541 expanded)
%              Number of equality atoms :    5 (  16 expanded)
%              Maximal formula depth    :   21 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > r1_orders_2 > v6_waybel_0 > r2_hidden > r1_tarski > m1_subset_1 > l1_waybel_0 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > l1_orders_2 > k2_partfun1 > k4_waybel_9 > u1_waybel_0 > k1_toler_1 > #nlpp > u1_struct_0 > u1_orders_2 > #skF_2 > #skF_7 > #skF_6 > #skF_4 > #skF_8 > #skF_5 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

tff(v6_waybel_0,type,(
    v6_waybel_0: ( $i * $i ) > $o )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_orders_2,type,(
    r1_orders_2: ( $i * $i * $i ) > $o )).

tff(k4_waybel_9,type,(
    k4_waybel_9: ( $i * $i * $i ) > $i )).

tff(k1_toler_1,type,(
    k1_toler_1: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff(u1_waybel_0,type,(
    u1_waybel_0: ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(l1_waybel_0,type,(
    l1_waybel_0: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_partfun1,type,(
    k2_partfun1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff(u1_orders_2,type,(
    u1_orders_2: $i > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_125,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & l1_struct_0(A) )
       => ! [B] :
            ( ( ~ v2_struct_0(B)
              & l1_waybel_0(B,A) )
           => ! [C] :
                ( m1_subset_1(C,u1_struct_0(B))
               => r1_tarski(u1_struct_0(k4_waybel_9(A,B,C)),u1_struct_0(B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_waybel_9)).

tff(f_57,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => ! [B] :
          ( l1_waybel_0(B,A)
         => l1_orders_2(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_waybel_0)).

tff(f_50,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).

tff(f_108,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A)
        & ~ v2_struct_0(B)
        & l1_waybel_0(B,A)
        & m1_subset_1(C,u1_struct_0(B)) )
     => ( v6_waybel_0(k4_waybel_9(A,B,C),A)
        & l1_waybel_0(k4_waybel_9(A,B,C),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_waybel_9)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_92,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & l1_waybel_0(B,A) )
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(B))
             => ! [D] :
                  ( ( v6_waybel_0(D,A)
                    & l1_waybel_0(D,A) )
                 => ( D = k4_waybel_9(A,B,C)
                  <=> ( ! [E] :
                          ( r2_hidden(E,u1_struct_0(D))
                        <=> ? [F] :
                              ( m1_subset_1(F,u1_struct_0(B))
                              & F = E
                              & r1_orders_2(B,C,F) ) )
                      & r2_relset_1(u1_struct_0(D),u1_struct_0(D),u1_orders_2(D),k1_toler_1(u1_orders_2(B),u1_struct_0(D)))
                      & u1_waybel_0(A,D) = k2_partfun1(u1_struct_0(B),u1_struct_0(A),u1_waybel_0(A,B),u1_struct_0(D)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_waybel_9)).

tff(f_38,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_46,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(c_58,plain,(
    ~ v2_struct_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_56,plain,(
    l1_struct_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_52,plain,(
    l1_waybel_0('#skF_7','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_61,plain,(
    ! [B_194,A_195] :
      ( l1_orders_2(B_194)
      | ~ l1_waybel_0(B_194,A_195)
      | ~ l1_struct_0(A_195) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_64,plain,
    ( l1_orders_2('#skF_7')
    | ~ l1_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_52,c_61])).

tff(c_67,plain,(
    l1_orders_2('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_64])).

tff(c_12,plain,(
    ! [A_9] :
      ( l1_struct_0(A_9)
      | ~ l1_orders_2(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_54,plain,(
    ~ v2_struct_0('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_50,plain,(
    m1_subset_1('#skF_8',u1_struct_0('#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_104,plain,(
    ! [A_217,B_218,C_219] :
      ( l1_waybel_0(k4_waybel_9(A_217,B_218,C_219),A_217)
      | ~ m1_subset_1(C_219,u1_struct_0(B_218))
      | ~ l1_waybel_0(B_218,A_217)
      | v2_struct_0(B_218)
      | ~ l1_struct_0(A_217)
      | v2_struct_0(A_217) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_106,plain,(
    ! [A_217] :
      ( l1_waybel_0(k4_waybel_9(A_217,'#skF_7','#skF_8'),A_217)
      | ~ l1_waybel_0('#skF_7',A_217)
      | v2_struct_0('#skF_7')
      | ~ l1_struct_0(A_217)
      | v2_struct_0(A_217) ) ),
    inference(resolution,[status(thm)],[c_50,c_104])).

tff(c_109,plain,(
    ! [A_217] :
      ( l1_waybel_0(k4_waybel_9(A_217,'#skF_7','#skF_8'),A_217)
      | ~ l1_waybel_0('#skF_7',A_217)
      | ~ l1_struct_0(A_217)
      | v2_struct_0(A_217) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_106])).

tff(c_46,plain,(
    ! [A_185,B_186,C_187] :
      ( v6_waybel_0(k4_waybel_9(A_185,B_186,C_187),A_185)
      | ~ m1_subset_1(C_187,u1_struct_0(B_186))
      | ~ l1_waybel_0(B_186,A_185)
      | v2_struct_0(B_186)
      | ~ l1_struct_0(A_185)
      | v2_struct_0(A_185) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_69,plain,(
    ! [A_198,B_199] :
      ( ~ r2_hidden('#skF_1'(A_198,B_199),B_199)
      | r1_tarski(A_198,B_199) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_74,plain,(
    ! [A_1] : r1_tarski(A_1,A_1) ),
    inference(resolution,[status(thm)],[c_6,c_69])).

tff(c_82,plain,(
    ! [C_203,B_204,A_205] :
      ( r2_hidden(C_203,B_204)
      | ~ r2_hidden(C_203,A_205)
      | ~ r1_tarski(A_205,B_204) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_88,plain,(
    ! [A_1,B_2,B_204] :
      ( r2_hidden('#skF_1'(A_1,B_2),B_204)
      | ~ r1_tarski(A_1,B_204)
      | r1_tarski(A_1,B_2) ) ),
    inference(resolution,[status(thm)],[c_6,c_82])).

tff(c_131,plain,(
    ! [A_234,B_235,C_236,E_237] :
      ( '#skF_2'(k4_waybel_9(A_234,B_235,C_236),B_235,A_234,E_237,C_236) = E_237
      | ~ r2_hidden(E_237,u1_struct_0(k4_waybel_9(A_234,B_235,C_236)))
      | ~ l1_waybel_0(k4_waybel_9(A_234,B_235,C_236),A_234)
      | ~ v6_waybel_0(k4_waybel_9(A_234,B_235,C_236),A_234)
      | ~ m1_subset_1(C_236,u1_struct_0(B_235))
      | ~ l1_waybel_0(B_235,A_234)
      | v2_struct_0(B_235)
      | ~ l1_struct_0(A_234)
      | v2_struct_0(A_234) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_236,plain,(
    ! [A_290,B_291,C_292,B_293] :
      ( '#skF_2'(k4_waybel_9(A_290,B_291,C_292),B_291,A_290,'#skF_1'(u1_struct_0(k4_waybel_9(A_290,B_291,C_292)),B_293),C_292) = '#skF_1'(u1_struct_0(k4_waybel_9(A_290,B_291,C_292)),B_293)
      | ~ l1_waybel_0(k4_waybel_9(A_290,B_291,C_292),A_290)
      | ~ v6_waybel_0(k4_waybel_9(A_290,B_291,C_292),A_290)
      | ~ m1_subset_1(C_292,u1_struct_0(B_291))
      | ~ l1_waybel_0(B_291,A_290)
      | v2_struct_0(B_291)
      | ~ l1_struct_0(A_290)
      | v2_struct_0(A_290)
      | r1_tarski(u1_struct_0(k4_waybel_9(A_290,B_291,C_292)),B_293) ) ),
    inference(resolution,[status(thm)],[c_6,c_131])).

tff(c_42,plain,(
    ! [A_13,B_101,C_145,E_178] :
      ( m1_subset_1('#skF_2'(k4_waybel_9(A_13,B_101,C_145),B_101,A_13,E_178,C_145),u1_struct_0(B_101))
      | ~ r2_hidden(E_178,u1_struct_0(k4_waybel_9(A_13,B_101,C_145)))
      | ~ l1_waybel_0(k4_waybel_9(A_13,B_101,C_145),A_13)
      | ~ v6_waybel_0(k4_waybel_9(A_13,B_101,C_145),A_13)
      | ~ m1_subset_1(C_145,u1_struct_0(B_101))
      | ~ l1_waybel_0(B_101,A_13)
      | v2_struct_0(B_101)
      | ~ l1_struct_0(A_13)
      | v2_struct_0(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_334,plain,(
    ! [A_334,B_335,C_336,B_337] :
      ( m1_subset_1('#skF_1'(u1_struct_0(k4_waybel_9(A_334,B_335,C_336)),B_337),u1_struct_0(B_335))
      | ~ r2_hidden('#skF_1'(u1_struct_0(k4_waybel_9(A_334,B_335,C_336)),B_337),u1_struct_0(k4_waybel_9(A_334,B_335,C_336)))
      | ~ l1_waybel_0(k4_waybel_9(A_334,B_335,C_336),A_334)
      | ~ v6_waybel_0(k4_waybel_9(A_334,B_335,C_336),A_334)
      | ~ m1_subset_1(C_336,u1_struct_0(B_335))
      | ~ l1_waybel_0(B_335,A_334)
      | v2_struct_0(B_335)
      | ~ l1_struct_0(A_334)
      | v2_struct_0(A_334)
      | ~ l1_waybel_0(k4_waybel_9(A_334,B_335,C_336),A_334)
      | ~ v6_waybel_0(k4_waybel_9(A_334,B_335,C_336),A_334)
      | ~ m1_subset_1(C_336,u1_struct_0(B_335))
      | ~ l1_waybel_0(B_335,A_334)
      | v2_struct_0(B_335)
      | ~ l1_struct_0(A_334)
      | v2_struct_0(A_334)
      | r1_tarski(u1_struct_0(k4_waybel_9(A_334,B_335,C_336)),B_337) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_236,c_42])).

tff(c_342,plain,(
    ! [A_334,B_335,C_336,B_2] :
      ( m1_subset_1('#skF_1'(u1_struct_0(k4_waybel_9(A_334,B_335,C_336)),B_2),u1_struct_0(B_335))
      | ~ l1_waybel_0(k4_waybel_9(A_334,B_335,C_336),A_334)
      | ~ v6_waybel_0(k4_waybel_9(A_334,B_335,C_336),A_334)
      | ~ m1_subset_1(C_336,u1_struct_0(B_335))
      | ~ l1_waybel_0(B_335,A_334)
      | v2_struct_0(B_335)
      | ~ l1_struct_0(A_334)
      | v2_struct_0(A_334)
      | ~ r1_tarski(u1_struct_0(k4_waybel_9(A_334,B_335,C_336)),u1_struct_0(k4_waybel_9(A_334,B_335,C_336)))
      | r1_tarski(u1_struct_0(k4_waybel_9(A_334,B_335,C_336)),B_2) ) ),
    inference(resolution,[status(thm)],[c_88,c_334])).

tff(c_359,plain,(
    ! [A_338,B_339,C_340,B_341] :
      ( m1_subset_1('#skF_1'(u1_struct_0(k4_waybel_9(A_338,B_339,C_340)),B_341),u1_struct_0(B_339))
      | ~ l1_waybel_0(k4_waybel_9(A_338,B_339,C_340),A_338)
      | ~ v6_waybel_0(k4_waybel_9(A_338,B_339,C_340),A_338)
      | ~ m1_subset_1(C_340,u1_struct_0(B_339))
      | ~ l1_waybel_0(B_339,A_338)
      | v2_struct_0(B_339)
      | ~ l1_struct_0(A_338)
      | v2_struct_0(A_338)
      | r1_tarski(u1_struct_0(k4_waybel_9(A_338,B_339,C_340)),B_341) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_342])).

tff(c_363,plain,(
    ! [A_342,B_343,C_344,B_345] :
      ( m1_subset_1('#skF_1'(u1_struct_0(k4_waybel_9(A_342,B_343,C_344)),B_345),u1_struct_0(B_343))
      | ~ l1_waybel_0(k4_waybel_9(A_342,B_343,C_344),A_342)
      | r1_tarski(u1_struct_0(k4_waybel_9(A_342,B_343,C_344)),B_345)
      | ~ m1_subset_1(C_344,u1_struct_0(B_343))
      | ~ l1_waybel_0(B_343,A_342)
      | v2_struct_0(B_343)
      | ~ l1_struct_0(A_342)
      | v2_struct_0(A_342) ) ),
    inference(resolution,[status(thm)],[c_46,c_359])).

tff(c_367,plain,(
    ! [A_217,B_345] :
      ( m1_subset_1('#skF_1'(u1_struct_0(k4_waybel_9(A_217,'#skF_7','#skF_8')),B_345),u1_struct_0('#skF_7'))
      | r1_tarski(u1_struct_0(k4_waybel_9(A_217,'#skF_7','#skF_8')),B_345)
      | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_7'))
      | v2_struct_0('#skF_7')
      | ~ l1_waybel_0('#skF_7',A_217)
      | ~ l1_struct_0(A_217)
      | v2_struct_0(A_217) ) ),
    inference(resolution,[status(thm)],[c_109,c_363])).

tff(c_371,plain,(
    ! [A_217,B_345] :
      ( m1_subset_1('#skF_1'(u1_struct_0(k4_waybel_9(A_217,'#skF_7','#skF_8')),B_345),u1_struct_0('#skF_7'))
      | r1_tarski(u1_struct_0(k4_waybel_9(A_217,'#skF_7','#skF_8')),B_345)
      | v2_struct_0('#skF_7')
      | ~ l1_waybel_0('#skF_7',A_217)
      | ~ l1_struct_0(A_217)
      | v2_struct_0(A_217) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_367])).

tff(c_373,plain,(
    ! [A_346,B_347] :
      ( m1_subset_1('#skF_1'(u1_struct_0(k4_waybel_9(A_346,'#skF_7','#skF_8')),B_347),u1_struct_0('#skF_7'))
      | r1_tarski(u1_struct_0(k4_waybel_9(A_346,'#skF_7','#skF_8')),B_347)
      | ~ l1_waybel_0('#skF_7',A_346)
      | ~ l1_struct_0(A_346)
      | v2_struct_0(A_346) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_371])).

tff(c_76,plain,(
    ! [A_201,B_202] :
      ( r2_hidden(A_201,B_202)
      | v1_xboole_0(B_202)
      | ~ m1_subset_1(A_201,B_202) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_81,plain,(
    ! [A_1,B_202] :
      ( r1_tarski(A_1,B_202)
      | v1_xboole_0(B_202)
      | ~ m1_subset_1('#skF_1'(A_1,B_202),B_202) ) ),
    inference(resolution,[status(thm)],[c_76,c_4])).

tff(c_391,plain,(
    ! [A_346] :
      ( v1_xboole_0(u1_struct_0('#skF_7'))
      | r1_tarski(u1_struct_0(k4_waybel_9(A_346,'#skF_7','#skF_8')),u1_struct_0('#skF_7'))
      | ~ l1_waybel_0('#skF_7',A_346)
      | ~ l1_struct_0(A_346)
      | v2_struct_0(A_346) ) ),
    inference(resolution,[status(thm)],[c_373,c_81])).

tff(c_392,plain,(
    v1_xboole_0(u1_struct_0('#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_391])).

tff(c_10,plain,(
    ! [A_8] :
      ( ~ v1_xboole_0(u1_struct_0(A_8))
      | ~ l1_struct_0(A_8)
      | v2_struct_0(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_395,plain,
    ( ~ l1_struct_0('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_392,c_10])).

tff(c_398,plain,(
    ~ l1_struct_0('#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_395])).

tff(c_401,plain,(
    ~ l1_orders_2('#skF_7') ),
    inference(resolution,[status(thm)],[c_12,c_398])).

tff(c_405,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_401])).

tff(c_408,plain,(
    ! [A_348] :
      ( r1_tarski(u1_struct_0(k4_waybel_9(A_348,'#skF_7','#skF_8')),u1_struct_0('#skF_7'))
      | ~ l1_waybel_0('#skF_7',A_348)
      | ~ l1_struct_0(A_348)
      | v2_struct_0(A_348) ) ),
    inference(splitRight,[status(thm)],[c_391])).

tff(c_48,plain,(
    ~ r1_tarski(u1_struct_0(k4_waybel_9('#skF_6','#skF_7','#skF_8')),u1_struct_0('#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_417,plain,
    ( ~ l1_waybel_0('#skF_7','#skF_6')
    | ~ l1_struct_0('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_408,c_48])).

tff(c_423,plain,(
    v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_52,c_417])).

tff(c_425,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_423])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:29:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.10/1.52  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.10/1.52  
% 3.10/1.52  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.10/1.53  %$ r2_relset_1 > r1_orders_2 > v6_waybel_0 > r2_hidden > r1_tarski > m1_subset_1 > l1_waybel_0 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > l1_orders_2 > k2_partfun1 > k4_waybel_9 > u1_waybel_0 > k1_toler_1 > #nlpp > u1_struct_0 > u1_orders_2 > #skF_2 > #skF_7 > #skF_6 > #skF_4 > #skF_8 > #skF_5 > #skF_3 > #skF_1
% 3.10/1.53  
% 3.10/1.53  %Foreground sorts:
% 3.10/1.53  
% 3.10/1.53  
% 3.10/1.53  %Background operators:
% 3.10/1.53  
% 3.10/1.53  
% 3.10/1.53  %Foreground operators:
% 3.10/1.53  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.10/1.53  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.10/1.53  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 3.10/1.53  tff(v6_waybel_0, type, v6_waybel_0: ($i * $i) > $o).
% 3.10/1.53  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.10/1.53  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i * $i) > $i).
% 3.10/1.53  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 3.10/1.53  tff(k4_waybel_9, type, k4_waybel_9: ($i * $i * $i) > $i).
% 3.10/1.53  tff(k1_toler_1, type, k1_toler_1: ($i * $i) > $i).
% 3.10/1.53  tff('#skF_7', type, '#skF_7': $i).
% 3.10/1.53  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.10/1.53  tff('#skF_6', type, '#skF_6': $i).
% 3.10/1.53  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.10/1.53  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 3.10/1.53  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 3.10/1.53  tff(u1_waybel_0, type, u1_waybel_0: ($i * $i) > $i).
% 3.10/1.53  tff('#skF_8', type, '#skF_8': $i).
% 3.10/1.53  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.10/1.53  tff(l1_waybel_0, type, l1_waybel_0: ($i * $i) > $o).
% 3.10/1.53  tff('#skF_5', type, '#skF_5': ($i * $i * $i * $i) > $i).
% 3.10/1.53  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.10/1.53  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 3.10/1.53  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 3.10/1.53  tff(u1_orders_2, type, u1_orders_2: $i > $i).
% 3.10/1.53  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.10/1.53  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.10/1.53  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.10/1.53  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.10/1.53  
% 3.31/1.54  tff(f_125, negated_conjecture, ~(![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: ((~v2_struct_0(B) & l1_waybel_0(B, A)) => (![C]: (m1_subset_1(C, u1_struct_0(B)) => r1_tarski(u1_struct_0(k4_waybel_9(A, B, C)), u1_struct_0(B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_waybel_9)).
% 3.31/1.54  tff(f_57, axiom, (![A]: (l1_struct_0(A) => (![B]: (l1_waybel_0(B, A) => l1_orders_2(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_waybel_0)).
% 3.31/1.54  tff(f_50, axiom, (![A]: (l1_orders_2(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 3.31/1.54  tff(f_108, axiom, (![A, B, C]: (((((~v2_struct_0(A) & l1_struct_0(A)) & ~v2_struct_0(B)) & l1_waybel_0(B, A)) & m1_subset_1(C, u1_struct_0(B))) => (v6_waybel_0(k4_waybel_9(A, B, C), A) & l1_waybel_0(k4_waybel_9(A, B, C), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k4_waybel_9)).
% 3.31/1.54  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 3.31/1.54  tff(f_92, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: ((~v2_struct_0(B) & l1_waybel_0(B, A)) => (![C]: (m1_subset_1(C, u1_struct_0(B)) => (![D]: ((v6_waybel_0(D, A) & l1_waybel_0(D, A)) => ((D = k4_waybel_9(A, B, C)) <=> (((![E]: (r2_hidden(E, u1_struct_0(D)) <=> (?[F]: ((m1_subset_1(F, u1_struct_0(B)) & (F = E)) & r1_orders_2(B, C, F))))) & r2_relset_1(u1_struct_0(D), u1_struct_0(D), u1_orders_2(D), k1_toler_1(u1_orders_2(B), u1_struct_0(D)))) & (u1_waybel_0(A, D) = k2_partfun1(u1_struct_0(B), u1_struct_0(A), u1_waybel_0(A, B), u1_struct_0(D))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_waybel_9)).
% 3.31/1.54  tff(f_38, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 3.31/1.54  tff(f_46, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 3.35/1.54  tff(c_58, plain, (~v2_struct_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_125])).
% 3.35/1.54  tff(c_56, plain, (l1_struct_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_125])).
% 3.35/1.54  tff(c_52, plain, (l1_waybel_0('#skF_7', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_125])).
% 3.35/1.54  tff(c_61, plain, (![B_194, A_195]: (l1_orders_2(B_194) | ~l1_waybel_0(B_194, A_195) | ~l1_struct_0(A_195))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.35/1.54  tff(c_64, plain, (l1_orders_2('#skF_7') | ~l1_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_52, c_61])).
% 3.35/1.54  tff(c_67, plain, (l1_orders_2('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_64])).
% 3.35/1.54  tff(c_12, plain, (![A_9]: (l1_struct_0(A_9) | ~l1_orders_2(A_9))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.35/1.54  tff(c_54, plain, (~v2_struct_0('#skF_7')), inference(cnfTransformation, [status(thm)], [f_125])).
% 3.35/1.54  tff(c_50, plain, (m1_subset_1('#skF_8', u1_struct_0('#skF_7'))), inference(cnfTransformation, [status(thm)], [f_125])).
% 3.35/1.54  tff(c_104, plain, (![A_217, B_218, C_219]: (l1_waybel_0(k4_waybel_9(A_217, B_218, C_219), A_217) | ~m1_subset_1(C_219, u1_struct_0(B_218)) | ~l1_waybel_0(B_218, A_217) | v2_struct_0(B_218) | ~l1_struct_0(A_217) | v2_struct_0(A_217))), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.35/1.54  tff(c_106, plain, (![A_217]: (l1_waybel_0(k4_waybel_9(A_217, '#skF_7', '#skF_8'), A_217) | ~l1_waybel_0('#skF_7', A_217) | v2_struct_0('#skF_7') | ~l1_struct_0(A_217) | v2_struct_0(A_217))), inference(resolution, [status(thm)], [c_50, c_104])).
% 3.35/1.54  tff(c_109, plain, (![A_217]: (l1_waybel_0(k4_waybel_9(A_217, '#skF_7', '#skF_8'), A_217) | ~l1_waybel_0('#skF_7', A_217) | ~l1_struct_0(A_217) | v2_struct_0(A_217))), inference(negUnitSimplification, [status(thm)], [c_54, c_106])).
% 3.35/1.54  tff(c_46, plain, (![A_185, B_186, C_187]: (v6_waybel_0(k4_waybel_9(A_185, B_186, C_187), A_185) | ~m1_subset_1(C_187, u1_struct_0(B_186)) | ~l1_waybel_0(B_186, A_185) | v2_struct_0(B_186) | ~l1_struct_0(A_185) | v2_struct_0(A_185))), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.35/1.54  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.35/1.54  tff(c_69, plain, (![A_198, B_199]: (~r2_hidden('#skF_1'(A_198, B_199), B_199) | r1_tarski(A_198, B_199))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.35/1.54  tff(c_74, plain, (![A_1]: (r1_tarski(A_1, A_1))), inference(resolution, [status(thm)], [c_6, c_69])).
% 3.35/1.54  tff(c_82, plain, (![C_203, B_204, A_205]: (r2_hidden(C_203, B_204) | ~r2_hidden(C_203, A_205) | ~r1_tarski(A_205, B_204))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.35/1.54  tff(c_88, plain, (![A_1, B_2, B_204]: (r2_hidden('#skF_1'(A_1, B_2), B_204) | ~r1_tarski(A_1, B_204) | r1_tarski(A_1, B_2))), inference(resolution, [status(thm)], [c_6, c_82])).
% 3.35/1.54  tff(c_131, plain, (![A_234, B_235, C_236, E_237]: ('#skF_2'(k4_waybel_9(A_234, B_235, C_236), B_235, A_234, E_237, C_236)=E_237 | ~r2_hidden(E_237, u1_struct_0(k4_waybel_9(A_234, B_235, C_236))) | ~l1_waybel_0(k4_waybel_9(A_234, B_235, C_236), A_234) | ~v6_waybel_0(k4_waybel_9(A_234, B_235, C_236), A_234) | ~m1_subset_1(C_236, u1_struct_0(B_235)) | ~l1_waybel_0(B_235, A_234) | v2_struct_0(B_235) | ~l1_struct_0(A_234) | v2_struct_0(A_234))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.35/1.54  tff(c_236, plain, (![A_290, B_291, C_292, B_293]: ('#skF_2'(k4_waybel_9(A_290, B_291, C_292), B_291, A_290, '#skF_1'(u1_struct_0(k4_waybel_9(A_290, B_291, C_292)), B_293), C_292)='#skF_1'(u1_struct_0(k4_waybel_9(A_290, B_291, C_292)), B_293) | ~l1_waybel_0(k4_waybel_9(A_290, B_291, C_292), A_290) | ~v6_waybel_0(k4_waybel_9(A_290, B_291, C_292), A_290) | ~m1_subset_1(C_292, u1_struct_0(B_291)) | ~l1_waybel_0(B_291, A_290) | v2_struct_0(B_291) | ~l1_struct_0(A_290) | v2_struct_0(A_290) | r1_tarski(u1_struct_0(k4_waybel_9(A_290, B_291, C_292)), B_293))), inference(resolution, [status(thm)], [c_6, c_131])).
% 3.35/1.54  tff(c_42, plain, (![A_13, B_101, C_145, E_178]: (m1_subset_1('#skF_2'(k4_waybel_9(A_13, B_101, C_145), B_101, A_13, E_178, C_145), u1_struct_0(B_101)) | ~r2_hidden(E_178, u1_struct_0(k4_waybel_9(A_13, B_101, C_145))) | ~l1_waybel_0(k4_waybel_9(A_13, B_101, C_145), A_13) | ~v6_waybel_0(k4_waybel_9(A_13, B_101, C_145), A_13) | ~m1_subset_1(C_145, u1_struct_0(B_101)) | ~l1_waybel_0(B_101, A_13) | v2_struct_0(B_101) | ~l1_struct_0(A_13) | v2_struct_0(A_13))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.35/1.54  tff(c_334, plain, (![A_334, B_335, C_336, B_337]: (m1_subset_1('#skF_1'(u1_struct_0(k4_waybel_9(A_334, B_335, C_336)), B_337), u1_struct_0(B_335)) | ~r2_hidden('#skF_1'(u1_struct_0(k4_waybel_9(A_334, B_335, C_336)), B_337), u1_struct_0(k4_waybel_9(A_334, B_335, C_336))) | ~l1_waybel_0(k4_waybel_9(A_334, B_335, C_336), A_334) | ~v6_waybel_0(k4_waybel_9(A_334, B_335, C_336), A_334) | ~m1_subset_1(C_336, u1_struct_0(B_335)) | ~l1_waybel_0(B_335, A_334) | v2_struct_0(B_335) | ~l1_struct_0(A_334) | v2_struct_0(A_334) | ~l1_waybel_0(k4_waybel_9(A_334, B_335, C_336), A_334) | ~v6_waybel_0(k4_waybel_9(A_334, B_335, C_336), A_334) | ~m1_subset_1(C_336, u1_struct_0(B_335)) | ~l1_waybel_0(B_335, A_334) | v2_struct_0(B_335) | ~l1_struct_0(A_334) | v2_struct_0(A_334) | r1_tarski(u1_struct_0(k4_waybel_9(A_334, B_335, C_336)), B_337))), inference(superposition, [status(thm), theory('equality')], [c_236, c_42])).
% 3.35/1.54  tff(c_342, plain, (![A_334, B_335, C_336, B_2]: (m1_subset_1('#skF_1'(u1_struct_0(k4_waybel_9(A_334, B_335, C_336)), B_2), u1_struct_0(B_335)) | ~l1_waybel_0(k4_waybel_9(A_334, B_335, C_336), A_334) | ~v6_waybel_0(k4_waybel_9(A_334, B_335, C_336), A_334) | ~m1_subset_1(C_336, u1_struct_0(B_335)) | ~l1_waybel_0(B_335, A_334) | v2_struct_0(B_335) | ~l1_struct_0(A_334) | v2_struct_0(A_334) | ~r1_tarski(u1_struct_0(k4_waybel_9(A_334, B_335, C_336)), u1_struct_0(k4_waybel_9(A_334, B_335, C_336))) | r1_tarski(u1_struct_0(k4_waybel_9(A_334, B_335, C_336)), B_2))), inference(resolution, [status(thm)], [c_88, c_334])).
% 3.35/1.54  tff(c_359, plain, (![A_338, B_339, C_340, B_341]: (m1_subset_1('#skF_1'(u1_struct_0(k4_waybel_9(A_338, B_339, C_340)), B_341), u1_struct_0(B_339)) | ~l1_waybel_0(k4_waybel_9(A_338, B_339, C_340), A_338) | ~v6_waybel_0(k4_waybel_9(A_338, B_339, C_340), A_338) | ~m1_subset_1(C_340, u1_struct_0(B_339)) | ~l1_waybel_0(B_339, A_338) | v2_struct_0(B_339) | ~l1_struct_0(A_338) | v2_struct_0(A_338) | r1_tarski(u1_struct_0(k4_waybel_9(A_338, B_339, C_340)), B_341))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_342])).
% 3.35/1.54  tff(c_363, plain, (![A_342, B_343, C_344, B_345]: (m1_subset_1('#skF_1'(u1_struct_0(k4_waybel_9(A_342, B_343, C_344)), B_345), u1_struct_0(B_343)) | ~l1_waybel_0(k4_waybel_9(A_342, B_343, C_344), A_342) | r1_tarski(u1_struct_0(k4_waybel_9(A_342, B_343, C_344)), B_345) | ~m1_subset_1(C_344, u1_struct_0(B_343)) | ~l1_waybel_0(B_343, A_342) | v2_struct_0(B_343) | ~l1_struct_0(A_342) | v2_struct_0(A_342))), inference(resolution, [status(thm)], [c_46, c_359])).
% 3.35/1.54  tff(c_367, plain, (![A_217, B_345]: (m1_subset_1('#skF_1'(u1_struct_0(k4_waybel_9(A_217, '#skF_7', '#skF_8')), B_345), u1_struct_0('#skF_7')) | r1_tarski(u1_struct_0(k4_waybel_9(A_217, '#skF_7', '#skF_8')), B_345) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_7')) | v2_struct_0('#skF_7') | ~l1_waybel_0('#skF_7', A_217) | ~l1_struct_0(A_217) | v2_struct_0(A_217))), inference(resolution, [status(thm)], [c_109, c_363])).
% 3.35/1.54  tff(c_371, plain, (![A_217, B_345]: (m1_subset_1('#skF_1'(u1_struct_0(k4_waybel_9(A_217, '#skF_7', '#skF_8')), B_345), u1_struct_0('#skF_7')) | r1_tarski(u1_struct_0(k4_waybel_9(A_217, '#skF_7', '#skF_8')), B_345) | v2_struct_0('#skF_7') | ~l1_waybel_0('#skF_7', A_217) | ~l1_struct_0(A_217) | v2_struct_0(A_217))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_367])).
% 3.35/1.54  tff(c_373, plain, (![A_346, B_347]: (m1_subset_1('#skF_1'(u1_struct_0(k4_waybel_9(A_346, '#skF_7', '#skF_8')), B_347), u1_struct_0('#skF_7')) | r1_tarski(u1_struct_0(k4_waybel_9(A_346, '#skF_7', '#skF_8')), B_347) | ~l1_waybel_0('#skF_7', A_346) | ~l1_struct_0(A_346) | v2_struct_0(A_346))), inference(negUnitSimplification, [status(thm)], [c_54, c_371])).
% 3.35/1.54  tff(c_76, plain, (![A_201, B_202]: (r2_hidden(A_201, B_202) | v1_xboole_0(B_202) | ~m1_subset_1(A_201, B_202))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.35/1.54  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.35/1.54  tff(c_81, plain, (![A_1, B_202]: (r1_tarski(A_1, B_202) | v1_xboole_0(B_202) | ~m1_subset_1('#skF_1'(A_1, B_202), B_202))), inference(resolution, [status(thm)], [c_76, c_4])).
% 3.35/1.54  tff(c_391, plain, (![A_346]: (v1_xboole_0(u1_struct_0('#skF_7')) | r1_tarski(u1_struct_0(k4_waybel_9(A_346, '#skF_7', '#skF_8')), u1_struct_0('#skF_7')) | ~l1_waybel_0('#skF_7', A_346) | ~l1_struct_0(A_346) | v2_struct_0(A_346))), inference(resolution, [status(thm)], [c_373, c_81])).
% 3.35/1.54  tff(c_392, plain, (v1_xboole_0(u1_struct_0('#skF_7'))), inference(splitLeft, [status(thm)], [c_391])).
% 3.35/1.54  tff(c_10, plain, (![A_8]: (~v1_xboole_0(u1_struct_0(A_8)) | ~l1_struct_0(A_8) | v2_struct_0(A_8))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.35/1.54  tff(c_395, plain, (~l1_struct_0('#skF_7') | v2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_392, c_10])).
% 3.35/1.54  tff(c_398, plain, (~l1_struct_0('#skF_7')), inference(negUnitSimplification, [status(thm)], [c_54, c_395])).
% 3.35/1.54  tff(c_401, plain, (~l1_orders_2('#skF_7')), inference(resolution, [status(thm)], [c_12, c_398])).
% 3.35/1.54  tff(c_405, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_67, c_401])).
% 3.35/1.54  tff(c_408, plain, (![A_348]: (r1_tarski(u1_struct_0(k4_waybel_9(A_348, '#skF_7', '#skF_8')), u1_struct_0('#skF_7')) | ~l1_waybel_0('#skF_7', A_348) | ~l1_struct_0(A_348) | v2_struct_0(A_348))), inference(splitRight, [status(thm)], [c_391])).
% 3.35/1.54  tff(c_48, plain, (~r1_tarski(u1_struct_0(k4_waybel_9('#skF_6', '#skF_7', '#skF_8')), u1_struct_0('#skF_7'))), inference(cnfTransformation, [status(thm)], [f_125])).
% 3.35/1.54  tff(c_417, plain, (~l1_waybel_0('#skF_7', '#skF_6') | ~l1_struct_0('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_408, c_48])).
% 3.35/1.54  tff(c_423, plain, (v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_52, c_417])).
% 3.35/1.54  tff(c_425, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_423])).
% 3.35/1.54  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.35/1.54  
% 3.35/1.54  Inference rules
% 3.35/1.54  ----------------------
% 3.35/1.54  #Ref     : 0
% 3.35/1.54  #Sup     : 72
% 3.35/1.54  #Fact    : 0
% 3.35/1.54  #Define  : 0
% 3.35/1.54  #Split   : 2
% 3.35/1.54  #Chain   : 0
% 3.35/1.54  #Close   : 0
% 3.35/1.54  
% 3.35/1.54  Ordering : KBO
% 3.35/1.54  
% 3.35/1.54  Simplification rules
% 3.35/1.54  ----------------------
% 3.35/1.54  #Subsume      : 10
% 3.35/1.54  #Demod        : 17
% 3.35/1.54  #Tautology    : 9
% 3.35/1.54  #SimpNegUnit  : 16
% 3.35/1.54  #BackRed      : 0
% 3.35/1.54  
% 3.35/1.54  #Partial instantiations: 0
% 3.35/1.54  #Strategies tried      : 1
% 3.35/1.54  
% 3.35/1.54  Timing (in seconds)
% 3.35/1.54  ----------------------
% 3.35/1.55  Preprocessing        : 0.37
% 3.35/1.55  Parsing              : 0.18
% 3.35/1.55  CNF conversion       : 0.04
% 3.35/1.55  Main loop            : 0.36
% 3.35/1.55  Inferencing          : 0.14
% 3.35/1.55  Reduction            : 0.09
% 3.35/1.55  Demodulation         : 0.06
% 3.35/1.55  BG Simplification    : 0.03
% 3.35/1.55  Subsumption          : 0.08
% 3.35/1.55  Abstraction          : 0.03
% 3.35/1.55  MUC search           : 0.00
% 3.35/1.55  Cooper               : 0.00
% 3.35/1.55  Total                : 0.76
% 3.35/1.55  Index Insertion      : 0.00
% 3.35/1.55  Index Deletion       : 0.00
% 3.35/1.55  Index Matching       : 0.00
% 3.35/1.55  BG Taut test         : 0.00
%------------------------------------------------------------------------------
