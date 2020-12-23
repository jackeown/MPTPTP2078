%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:31:09 EST 2020

% Result     : Theorem 4.39s
% Output     : CNFRefutation 4.39s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 147 expanded)
%              Number of leaves         :   36 (  68 expanded)
%              Depth                    :   15
%              Number of atoms          :  209 ( 541 expanded)
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

tff(f_123,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & l1_struct_0(A) )
       => ! [B] :
            ( ( ~ v2_struct_0(B)
              & l1_waybel_0(B,A) )
           => ! [C] :
                ( m1_subset_1(C,u1_struct_0(B))
               => r1_tarski(u1_struct_0(k4_waybel_9(A,B,C)),u1_struct_0(B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_waybel_9)).

tff(f_49,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => ! [B] :
          ( l1_waybel_0(B,A)
         => l1_orders_2(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_waybel_0)).

tff(f_42,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).

tff(f_106,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A)
        & ~ v2_struct_0(B)
        & l1_waybel_0(B,A)
        & m1_subset_1(C,u1_struct_0(B)) )
     => ( v6_waybel_0(k4_waybel_9(A,B,C),A)
        & l1_waybel_0(k4_waybel_9(A,B,C),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_waybel_9)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_90,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_waybel_9)).

tff(f_38,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_55,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => ( v2_struct_0(A)
      <=> v1_xboole_0(u1_struct_0(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_struct_0)).

tff(c_60,plain,(
    ~ v2_struct_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_58,plain,(
    l1_struct_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_54,plain,(
    l1_waybel_0('#skF_7','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_63,plain,(
    ! [B_194,A_195] :
      ( l1_orders_2(B_194)
      | ~ l1_waybel_0(B_194,A_195)
      | ~ l1_struct_0(A_195) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_66,plain,
    ( l1_orders_2('#skF_7')
    | ~ l1_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_54,c_63])).

tff(c_69,plain,(
    l1_orders_2('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_66])).

tff(c_10,plain,(
    ! [A_8] :
      ( l1_struct_0(A_8)
      | ~ l1_orders_2(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_56,plain,(
    ~ v2_struct_0('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_52,plain,(
    m1_subset_1('#skF_8',u1_struct_0('#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_115,plain,(
    ! [A_222,B_223,C_224] :
      ( l1_waybel_0(k4_waybel_9(A_222,B_223,C_224),A_222)
      | ~ m1_subset_1(C_224,u1_struct_0(B_223))
      | ~ l1_waybel_0(B_223,A_222)
      | v2_struct_0(B_223)
      | ~ l1_struct_0(A_222)
      | v2_struct_0(A_222) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_117,plain,(
    ! [A_222] :
      ( l1_waybel_0(k4_waybel_9(A_222,'#skF_7','#skF_8'),A_222)
      | ~ l1_waybel_0('#skF_7',A_222)
      | v2_struct_0('#skF_7')
      | ~ l1_struct_0(A_222)
      | v2_struct_0(A_222) ) ),
    inference(resolution,[status(thm)],[c_52,c_115])).

tff(c_120,plain,(
    ! [A_222] :
      ( l1_waybel_0(k4_waybel_9(A_222,'#skF_7','#skF_8'),A_222)
      | ~ l1_waybel_0('#skF_7',A_222)
      | ~ l1_struct_0(A_222)
      | v2_struct_0(A_222) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_117])).

tff(c_48,plain,(
    ! [A_185,B_186,C_187] :
      ( v6_waybel_0(k4_waybel_9(A_185,B_186,C_187),A_185)
      | ~ m1_subset_1(C_187,u1_struct_0(B_186))
      | ~ l1_waybel_0(B_186,A_185)
      | v2_struct_0(B_186)
      | ~ l1_struct_0(A_185)
      | v2_struct_0(A_185) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_82,plain,(
    ! [A_201,B_202] :
      ( r2_hidden('#skF_1'(A_201,B_202),A_201)
      | r1_tarski(A_201,B_202) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_87,plain,(
    ! [A_201] : r1_tarski(A_201,A_201) ),
    inference(resolution,[status(thm)],[c_82,c_4])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_89,plain,(
    ! [C_204,B_205,A_206] :
      ( r2_hidden(C_204,B_205)
      | ~ r2_hidden(C_204,A_206)
      | ~ r1_tarski(A_206,B_205) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_94,plain,(
    ! [A_1,B_2,B_205] :
      ( r2_hidden('#skF_1'(A_1,B_2),B_205)
      | ~ r1_tarski(A_1,B_205)
      | r1_tarski(A_1,B_2) ) ),
    inference(resolution,[status(thm)],[c_6,c_89])).

tff(c_131,plain,(
    ! [A_231,B_232,C_233,E_234] :
      ( '#skF_2'(k4_waybel_9(A_231,B_232,C_233),B_232,A_231,E_234,C_233) = E_234
      | ~ r2_hidden(E_234,u1_struct_0(k4_waybel_9(A_231,B_232,C_233)))
      | ~ l1_waybel_0(k4_waybel_9(A_231,B_232,C_233),A_231)
      | ~ v6_waybel_0(k4_waybel_9(A_231,B_232,C_233),A_231)
      | ~ m1_subset_1(C_233,u1_struct_0(B_232))
      | ~ l1_waybel_0(B_232,A_231)
      | v2_struct_0(B_232)
      | ~ l1_struct_0(A_231)
      | v2_struct_0(A_231) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_290,plain,(
    ! [A_299,B_300,C_301,B_302] :
      ( '#skF_2'(k4_waybel_9(A_299,B_300,C_301),B_300,A_299,'#skF_1'(u1_struct_0(k4_waybel_9(A_299,B_300,C_301)),B_302),C_301) = '#skF_1'(u1_struct_0(k4_waybel_9(A_299,B_300,C_301)),B_302)
      | ~ l1_waybel_0(k4_waybel_9(A_299,B_300,C_301),A_299)
      | ~ v6_waybel_0(k4_waybel_9(A_299,B_300,C_301),A_299)
      | ~ m1_subset_1(C_301,u1_struct_0(B_300))
      | ~ l1_waybel_0(B_300,A_299)
      | v2_struct_0(B_300)
      | ~ l1_struct_0(A_299)
      | v2_struct_0(A_299)
      | r1_tarski(u1_struct_0(k4_waybel_9(A_299,B_300,C_301)),B_302) ) ),
    inference(resolution,[status(thm)],[c_6,c_131])).

tff(c_44,plain,(
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
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_679,plain,(
    ! [A_440,B_441,C_442,B_443] :
      ( m1_subset_1('#skF_1'(u1_struct_0(k4_waybel_9(A_440,B_441,C_442)),B_443),u1_struct_0(B_441))
      | ~ r2_hidden('#skF_1'(u1_struct_0(k4_waybel_9(A_440,B_441,C_442)),B_443),u1_struct_0(k4_waybel_9(A_440,B_441,C_442)))
      | ~ l1_waybel_0(k4_waybel_9(A_440,B_441,C_442),A_440)
      | ~ v6_waybel_0(k4_waybel_9(A_440,B_441,C_442),A_440)
      | ~ m1_subset_1(C_442,u1_struct_0(B_441))
      | ~ l1_waybel_0(B_441,A_440)
      | v2_struct_0(B_441)
      | ~ l1_struct_0(A_440)
      | v2_struct_0(A_440)
      | ~ l1_waybel_0(k4_waybel_9(A_440,B_441,C_442),A_440)
      | ~ v6_waybel_0(k4_waybel_9(A_440,B_441,C_442),A_440)
      | ~ m1_subset_1(C_442,u1_struct_0(B_441))
      | ~ l1_waybel_0(B_441,A_440)
      | v2_struct_0(B_441)
      | ~ l1_struct_0(A_440)
      | v2_struct_0(A_440)
      | r1_tarski(u1_struct_0(k4_waybel_9(A_440,B_441,C_442)),B_443) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_290,c_44])).

tff(c_687,plain,(
    ! [A_440,B_441,C_442,B_2] :
      ( m1_subset_1('#skF_1'(u1_struct_0(k4_waybel_9(A_440,B_441,C_442)),B_2),u1_struct_0(B_441))
      | ~ l1_waybel_0(k4_waybel_9(A_440,B_441,C_442),A_440)
      | ~ v6_waybel_0(k4_waybel_9(A_440,B_441,C_442),A_440)
      | ~ m1_subset_1(C_442,u1_struct_0(B_441))
      | ~ l1_waybel_0(B_441,A_440)
      | v2_struct_0(B_441)
      | ~ l1_struct_0(A_440)
      | v2_struct_0(A_440)
      | ~ r1_tarski(u1_struct_0(k4_waybel_9(A_440,B_441,C_442)),u1_struct_0(k4_waybel_9(A_440,B_441,C_442)))
      | r1_tarski(u1_struct_0(k4_waybel_9(A_440,B_441,C_442)),B_2) ) ),
    inference(resolution,[status(thm)],[c_94,c_679])).

tff(c_704,plain,(
    ! [A_444,B_445,C_446,B_447] :
      ( m1_subset_1('#skF_1'(u1_struct_0(k4_waybel_9(A_444,B_445,C_446)),B_447),u1_struct_0(B_445))
      | ~ l1_waybel_0(k4_waybel_9(A_444,B_445,C_446),A_444)
      | ~ v6_waybel_0(k4_waybel_9(A_444,B_445,C_446),A_444)
      | ~ m1_subset_1(C_446,u1_struct_0(B_445))
      | ~ l1_waybel_0(B_445,A_444)
      | v2_struct_0(B_445)
      | ~ l1_struct_0(A_444)
      | v2_struct_0(A_444)
      | r1_tarski(u1_struct_0(k4_waybel_9(A_444,B_445,C_446)),B_447) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_687])).

tff(c_708,plain,(
    ! [A_448,B_449,C_450,B_451] :
      ( m1_subset_1('#skF_1'(u1_struct_0(k4_waybel_9(A_448,B_449,C_450)),B_451),u1_struct_0(B_449))
      | ~ l1_waybel_0(k4_waybel_9(A_448,B_449,C_450),A_448)
      | r1_tarski(u1_struct_0(k4_waybel_9(A_448,B_449,C_450)),B_451)
      | ~ m1_subset_1(C_450,u1_struct_0(B_449))
      | ~ l1_waybel_0(B_449,A_448)
      | v2_struct_0(B_449)
      | ~ l1_struct_0(A_448)
      | v2_struct_0(A_448) ) ),
    inference(resolution,[status(thm)],[c_48,c_704])).

tff(c_714,plain,(
    ! [A_222,B_451] :
      ( m1_subset_1('#skF_1'(u1_struct_0(k4_waybel_9(A_222,'#skF_7','#skF_8')),B_451),u1_struct_0('#skF_7'))
      | r1_tarski(u1_struct_0(k4_waybel_9(A_222,'#skF_7','#skF_8')),B_451)
      | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_7'))
      | v2_struct_0('#skF_7')
      | ~ l1_waybel_0('#skF_7',A_222)
      | ~ l1_struct_0(A_222)
      | v2_struct_0(A_222) ) ),
    inference(resolution,[status(thm)],[c_120,c_708])).

tff(c_719,plain,(
    ! [A_222,B_451] :
      ( m1_subset_1('#skF_1'(u1_struct_0(k4_waybel_9(A_222,'#skF_7','#skF_8')),B_451),u1_struct_0('#skF_7'))
      | r1_tarski(u1_struct_0(k4_waybel_9(A_222,'#skF_7','#skF_8')),B_451)
      | v2_struct_0('#skF_7')
      | ~ l1_waybel_0('#skF_7',A_222)
      | ~ l1_struct_0(A_222)
      | v2_struct_0(A_222) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_714])).

tff(c_721,plain,(
    ! [A_452,B_453] :
      ( m1_subset_1('#skF_1'(u1_struct_0(k4_waybel_9(A_452,'#skF_7','#skF_8')),B_453),u1_struct_0('#skF_7'))
      | r1_tarski(u1_struct_0(k4_waybel_9(A_452,'#skF_7','#skF_8')),B_453)
      | ~ l1_waybel_0('#skF_7',A_452)
      | ~ l1_struct_0(A_452)
      | v2_struct_0(A_452) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_719])).

tff(c_8,plain,(
    ! [A_6,B_7] :
      ( r2_hidden(A_6,B_7)
      | v1_xboole_0(B_7)
      | ~ m1_subset_1(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_76,plain,(
    ! [A_199,B_200] :
      ( ~ r2_hidden('#skF_1'(A_199,B_200),B_200)
      | r1_tarski(A_199,B_200) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_81,plain,(
    ! [A_199,B_7] :
      ( r1_tarski(A_199,B_7)
      | v1_xboole_0(B_7)
      | ~ m1_subset_1('#skF_1'(A_199,B_7),B_7) ) ),
    inference(resolution,[status(thm)],[c_8,c_76])).

tff(c_739,plain,(
    ! [A_452] :
      ( v1_xboole_0(u1_struct_0('#skF_7'))
      | r1_tarski(u1_struct_0(k4_waybel_9(A_452,'#skF_7','#skF_8')),u1_struct_0('#skF_7'))
      | ~ l1_waybel_0('#skF_7',A_452)
      | ~ l1_struct_0(A_452)
      | v2_struct_0(A_452) ) ),
    inference(resolution,[status(thm)],[c_721,c_81])).

tff(c_744,plain,(
    v1_xboole_0(u1_struct_0('#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_739])).

tff(c_14,plain,(
    ! [A_12] :
      ( v2_struct_0(A_12)
      | ~ v1_xboole_0(u1_struct_0(A_12))
      | ~ l1_struct_0(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_747,plain,
    ( v2_struct_0('#skF_7')
    | ~ l1_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_744,c_14])).

tff(c_750,plain,(
    ~ l1_struct_0('#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_747])).

tff(c_753,plain,(
    ~ l1_orders_2('#skF_7') ),
    inference(resolution,[status(thm)],[c_10,c_750])).

tff(c_757,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_753])).

tff(c_789,plain,(
    ! [A_461] :
      ( r1_tarski(u1_struct_0(k4_waybel_9(A_461,'#skF_7','#skF_8')),u1_struct_0('#skF_7'))
      | ~ l1_waybel_0('#skF_7',A_461)
      | ~ l1_struct_0(A_461)
      | v2_struct_0(A_461) ) ),
    inference(splitRight,[status(thm)],[c_739])).

tff(c_50,plain,(
    ~ r1_tarski(u1_struct_0(k4_waybel_9('#skF_6','#skF_7','#skF_8')),u1_struct_0('#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_806,plain,
    ( ~ l1_waybel_0('#skF_7','#skF_6')
    | ~ l1_struct_0('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_789,c_50])).

tff(c_816,plain,(
    v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_54,c_806])).

tff(c_818,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_816])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:44:12 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.39/1.90  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.39/1.90  
% 4.39/1.90  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.39/1.91  %$ r2_relset_1 > r1_orders_2 > v6_waybel_0 > r2_hidden > r1_tarski > m1_subset_1 > l1_waybel_0 > v2_struct_0 > v1_xboole_0 > l1_struct_0 > l1_orders_2 > k2_partfun1 > k4_waybel_9 > u1_waybel_0 > k1_toler_1 > #nlpp > u1_struct_0 > u1_orders_2 > #skF_2 > #skF_7 > #skF_6 > #skF_4 > #skF_8 > #skF_5 > #skF_3 > #skF_1
% 4.39/1.91  
% 4.39/1.91  %Foreground sorts:
% 4.39/1.91  
% 4.39/1.91  
% 4.39/1.91  %Background operators:
% 4.39/1.91  
% 4.39/1.91  
% 4.39/1.91  %Foreground operators:
% 4.39/1.91  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.39/1.91  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.39/1.91  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 4.39/1.91  tff(v6_waybel_0, type, v6_waybel_0: ($i * $i) > $o).
% 4.39/1.91  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.39/1.91  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i * $i) > $i).
% 4.39/1.91  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 4.39/1.91  tff(k4_waybel_9, type, k4_waybel_9: ($i * $i * $i) > $i).
% 4.39/1.91  tff(k1_toler_1, type, k1_toler_1: ($i * $i) > $i).
% 4.39/1.91  tff('#skF_7', type, '#skF_7': $i).
% 4.39/1.91  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.39/1.91  tff('#skF_6', type, '#skF_6': $i).
% 4.39/1.91  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 4.39/1.91  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 4.39/1.91  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 4.39/1.91  tff(u1_waybel_0, type, u1_waybel_0: ($i * $i) > $i).
% 4.39/1.91  tff('#skF_8', type, '#skF_8': $i).
% 4.39/1.91  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.39/1.91  tff(l1_waybel_0, type, l1_waybel_0: ($i * $i) > $o).
% 4.39/1.91  tff('#skF_5', type, '#skF_5': ($i * $i * $i * $i) > $i).
% 4.39/1.91  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.39/1.91  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 4.39/1.91  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 4.39/1.91  tff(u1_orders_2, type, u1_orders_2: $i > $i).
% 4.39/1.91  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.39/1.91  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.39/1.91  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.39/1.91  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.39/1.91  
% 4.39/1.92  tff(f_123, negated_conjecture, ~(![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: ((~v2_struct_0(B) & l1_waybel_0(B, A)) => (![C]: (m1_subset_1(C, u1_struct_0(B)) => r1_tarski(u1_struct_0(k4_waybel_9(A, B, C)), u1_struct_0(B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_waybel_9)).
% 4.39/1.92  tff(f_49, axiom, (![A]: (l1_struct_0(A) => (![B]: (l1_waybel_0(B, A) => l1_orders_2(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_waybel_0)).
% 4.39/1.92  tff(f_42, axiom, (![A]: (l1_orders_2(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 4.39/1.92  tff(f_106, axiom, (![A, B, C]: (((((~v2_struct_0(A) & l1_struct_0(A)) & ~v2_struct_0(B)) & l1_waybel_0(B, A)) & m1_subset_1(C, u1_struct_0(B))) => (v6_waybel_0(k4_waybel_9(A, B, C), A) & l1_waybel_0(k4_waybel_9(A, B, C), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k4_waybel_9)).
% 4.39/1.92  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 4.39/1.92  tff(f_90, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: ((~v2_struct_0(B) & l1_waybel_0(B, A)) => (![C]: (m1_subset_1(C, u1_struct_0(B)) => (![D]: ((v6_waybel_0(D, A) & l1_waybel_0(D, A)) => ((D = k4_waybel_9(A, B, C)) <=> (((![E]: (r2_hidden(E, u1_struct_0(D)) <=> (?[F]: ((m1_subset_1(F, u1_struct_0(B)) & (F = E)) & r1_orders_2(B, C, F))))) & r2_relset_1(u1_struct_0(D), u1_struct_0(D), u1_orders_2(D), k1_toler_1(u1_orders_2(B), u1_struct_0(D)))) & (u1_waybel_0(A, D) = k2_partfun1(u1_struct_0(B), u1_struct_0(A), u1_waybel_0(A, B), u1_struct_0(D))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_waybel_9)).
% 4.39/1.92  tff(f_38, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 4.39/1.92  tff(f_55, axiom, (![A]: (l1_struct_0(A) => (v2_struct_0(A) <=> v1_xboole_0(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_struct_0)).
% 4.39/1.92  tff(c_60, plain, (~v2_struct_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_123])).
% 4.39/1.92  tff(c_58, plain, (l1_struct_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_123])).
% 4.39/1.92  tff(c_54, plain, (l1_waybel_0('#skF_7', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_123])).
% 4.39/1.92  tff(c_63, plain, (![B_194, A_195]: (l1_orders_2(B_194) | ~l1_waybel_0(B_194, A_195) | ~l1_struct_0(A_195))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.39/1.92  tff(c_66, plain, (l1_orders_2('#skF_7') | ~l1_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_54, c_63])).
% 4.39/1.92  tff(c_69, plain, (l1_orders_2('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_66])).
% 4.39/1.92  tff(c_10, plain, (![A_8]: (l1_struct_0(A_8) | ~l1_orders_2(A_8))), inference(cnfTransformation, [status(thm)], [f_42])).
% 4.39/1.92  tff(c_56, plain, (~v2_struct_0('#skF_7')), inference(cnfTransformation, [status(thm)], [f_123])).
% 4.39/1.92  tff(c_52, plain, (m1_subset_1('#skF_8', u1_struct_0('#skF_7'))), inference(cnfTransformation, [status(thm)], [f_123])).
% 4.39/1.92  tff(c_115, plain, (![A_222, B_223, C_224]: (l1_waybel_0(k4_waybel_9(A_222, B_223, C_224), A_222) | ~m1_subset_1(C_224, u1_struct_0(B_223)) | ~l1_waybel_0(B_223, A_222) | v2_struct_0(B_223) | ~l1_struct_0(A_222) | v2_struct_0(A_222))), inference(cnfTransformation, [status(thm)], [f_106])).
% 4.39/1.92  tff(c_117, plain, (![A_222]: (l1_waybel_0(k4_waybel_9(A_222, '#skF_7', '#skF_8'), A_222) | ~l1_waybel_0('#skF_7', A_222) | v2_struct_0('#skF_7') | ~l1_struct_0(A_222) | v2_struct_0(A_222))), inference(resolution, [status(thm)], [c_52, c_115])).
% 4.39/1.92  tff(c_120, plain, (![A_222]: (l1_waybel_0(k4_waybel_9(A_222, '#skF_7', '#skF_8'), A_222) | ~l1_waybel_0('#skF_7', A_222) | ~l1_struct_0(A_222) | v2_struct_0(A_222))), inference(negUnitSimplification, [status(thm)], [c_56, c_117])).
% 4.39/1.92  tff(c_48, plain, (![A_185, B_186, C_187]: (v6_waybel_0(k4_waybel_9(A_185, B_186, C_187), A_185) | ~m1_subset_1(C_187, u1_struct_0(B_186)) | ~l1_waybel_0(B_186, A_185) | v2_struct_0(B_186) | ~l1_struct_0(A_185) | v2_struct_0(A_185))), inference(cnfTransformation, [status(thm)], [f_106])).
% 4.39/1.92  tff(c_82, plain, (![A_201, B_202]: (r2_hidden('#skF_1'(A_201, B_202), A_201) | r1_tarski(A_201, B_202))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.39/1.92  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.39/1.92  tff(c_87, plain, (![A_201]: (r1_tarski(A_201, A_201))), inference(resolution, [status(thm)], [c_82, c_4])).
% 4.39/1.92  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.39/1.92  tff(c_89, plain, (![C_204, B_205, A_206]: (r2_hidden(C_204, B_205) | ~r2_hidden(C_204, A_206) | ~r1_tarski(A_206, B_205))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.39/1.92  tff(c_94, plain, (![A_1, B_2, B_205]: (r2_hidden('#skF_1'(A_1, B_2), B_205) | ~r1_tarski(A_1, B_205) | r1_tarski(A_1, B_2))), inference(resolution, [status(thm)], [c_6, c_89])).
% 4.39/1.92  tff(c_131, plain, (![A_231, B_232, C_233, E_234]: ('#skF_2'(k4_waybel_9(A_231, B_232, C_233), B_232, A_231, E_234, C_233)=E_234 | ~r2_hidden(E_234, u1_struct_0(k4_waybel_9(A_231, B_232, C_233))) | ~l1_waybel_0(k4_waybel_9(A_231, B_232, C_233), A_231) | ~v6_waybel_0(k4_waybel_9(A_231, B_232, C_233), A_231) | ~m1_subset_1(C_233, u1_struct_0(B_232)) | ~l1_waybel_0(B_232, A_231) | v2_struct_0(B_232) | ~l1_struct_0(A_231) | v2_struct_0(A_231))), inference(cnfTransformation, [status(thm)], [f_90])).
% 4.39/1.92  tff(c_290, plain, (![A_299, B_300, C_301, B_302]: ('#skF_2'(k4_waybel_9(A_299, B_300, C_301), B_300, A_299, '#skF_1'(u1_struct_0(k4_waybel_9(A_299, B_300, C_301)), B_302), C_301)='#skF_1'(u1_struct_0(k4_waybel_9(A_299, B_300, C_301)), B_302) | ~l1_waybel_0(k4_waybel_9(A_299, B_300, C_301), A_299) | ~v6_waybel_0(k4_waybel_9(A_299, B_300, C_301), A_299) | ~m1_subset_1(C_301, u1_struct_0(B_300)) | ~l1_waybel_0(B_300, A_299) | v2_struct_0(B_300) | ~l1_struct_0(A_299) | v2_struct_0(A_299) | r1_tarski(u1_struct_0(k4_waybel_9(A_299, B_300, C_301)), B_302))), inference(resolution, [status(thm)], [c_6, c_131])).
% 4.39/1.92  tff(c_44, plain, (![A_13, B_101, C_145, E_178]: (m1_subset_1('#skF_2'(k4_waybel_9(A_13, B_101, C_145), B_101, A_13, E_178, C_145), u1_struct_0(B_101)) | ~r2_hidden(E_178, u1_struct_0(k4_waybel_9(A_13, B_101, C_145))) | ~l1_waybel_0(k4_waybel_9(A_13, B_101, C_145), A_13) | ~v6_waybel_0(k4_waybel_9(A_13, B_101, C_145), A_13) | ~m1_subset_1(C_145, u1_struct_0(B_101)) | ~l1_waybel_0(B_101, A_13) | v2_struct_0(B_101) | ~l1_struct_0(A_13) | v2_struct_0(A_13))), inference(cnfTransformation, [status(thm)], [f_90])).
% 4.39/1.92  tff(c_679, plain, (![A_440, B_441, C_442, B_443]: (m1_subset_1('#skF_1'(u1_struct_0(k4_waybel_9(A_440, B_441, C_442)), B_443), u1_struct_0(B_441)) | ~r2_hidden('#skF_1'(u1_struct_0(k4_waybel_9(A_440, B_441, C_442)), B_443), u1_struct_0(k4_waybel_9(A_440, B_441, C_442))) | ~l1_waybel_0(k4_waybel_9(A_440, B_441, C_442), A_440) | ~v6_waybel_0(k4_waybel_9(A_440, B_441, C_442), A_440) | ~m1_subset_1(C_442, u1_struct_0(B_441)) | ~l1_waybel_0(B_441, A_440) | v2_struct_0(B_441) | ~l1_struct_0(A_440) | v2_struct_0(A_440) | ~l1_waybel_0(k4_waybel_9(A_440, B_441, C_442), A_440) | ~v6_waybel_0(k4_waybel_9(A_440, B_441, C_442), A_440) | ~m1_subset_1(C_442, u1_struct_0(B_441)) | ~l1_waybel_0(B_441, A_440) | v2_struct_0(B_441) | ~l1_struct_0(A_440) | v2_struct_0(A_440) | r1_tarski(u1_struct_0(k4_waybel_9(A_440, B_441, C_442)), B_443))), inference(superposition, [status(thm), theory('equality')], [c_290, c_44])).
% 4.39/1.92  tff(c_687, plain, (![A_440, B_441, C_442, B_2]: (m1_subset_1('#skF_1'(u1_struct_0(k4_waybel_9(A_440, B_441, C_442)), B_2), u1_struct_0(B_441)) | ~l1_waybel_0(k4_waybel_9(A_440, B_441, C_442), A_440) | ~v6_waybel_0(k4_waybel_9(A_440, B_441, C_442), A_440) | ~m1_subset_1(C_442, u1_struct_0(B_441)) | ~l1_waybel_0(B_441, A_440) | v2_struct_0(B_441) | ~l1_struct_0(A_440) | v2_struct_0(A_440) | ~r1_tarski(u1_struct_0(k4_waybel_9(A_440, B_441, C_442)), u1_struct_0(k4_waybel_9(A_440, B_441, C_442))) | r1_tarski(u1_struct_0(k4_waybel_9(A_440, B_441, C_442)), B_2))), inference(resolution, [status(thm)], [c_94, c_679])).
% 4.39/1.92  tff(c_704, plain, (![A_444, B_445, C_446, B_447]: (m1_subset_1('#skF_1'(u1_struct_0(k4_waybel_9(A_444, B_445, C_446)), B_447), u1_struct_0(B_445)) | ~l1_waybel_0(k4_waybel_9(A_444, B_445, C_446), A_444) | ~v6_waybel_0(k4_waybel_9(A_444, B_445, C_446), A_444) | ~m1_subset_1(C_446, u1_struct_0(B_445)) | ~l1_waybel_0(B_445, A_444) | v2_struct_0(B_445) | ~l1_struct_0(A_444) | v2_struct_0(A_444) | r1_tarski(u1_struct_0(k4_waybel_9(A_444, B_445, C_446)), B_447))), inference(demodulation, [status(thm), theory('equality')], [c_87, c_687])).
% 4.39/1.92  tff(c_708, plain, (![A_448, B_449, C_450, B_451]: (m1_subset_1('#skF_1'(u1_struct_0(k4_waybel_9(A_448, B_449, C_450)), B_451), u1_struct_0(B_449)) | ~l1_waybel_0(k4_waybel_9(A_448, B_449, C_450), A_448) | r1_tarski(u1_struct_0(k4_waybel_9(A_448, B_449, C_450)), B_451) | ~m1_subset_1(C_450, u1_struct_0(B_449)) | ~l1_waybel_0(B_449, A_448) | v2_struct_0(B_449) | ~l1_struct_0(A_448) | v2_struct_0(A_448))), inference(resolution, [status(thm)], [c_48, c_704])).
% 4.39/1.92  tff(c_714, plain, (![A_222, B_451]: (m1_subset_1('#skF_1'(u1_struct_0(k4_waybel_9(A_222, '#skF_7', '#skF_8')), B_451), u1_struct_0('#skF_7')) | r1_tarski(u1_struct_0(k4_waybel_9(A_222, '#skF_7', '#skF_8')), B_451) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_7')) | v2_struct_0('#skF_7') | ~l1_waybel_0('#skF_7', A_222) | ~l1_struct_0(A_222) | v2_struct_0(A_222))), inference(resolution, [status(thm)], [c_120, c_708])).
% 4.39/1.92  tff(c_719, plain, (![A_222, B_451]: (m1_subset_1('#skF_1'(u1_struct_0(k4_waybel_9(A_222, '#skF_7', '#skF_8')), B_451), u1_struct_0('#skF_7')) | r1_tarski(u1_struct_0(k4_waybel_9(A_222, '#skF_7', '#skF_8')), B_451) | v2_struct_0('#skF_7') | ~l1_waybel_0('#skF_7', A_222) | ~l1_struct_0(A_222) | v2_struct_0(A_222))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_714])).
% 4.39/1.92  tff(c_721, plain, (![A_452, B_453]: (m1_subset_1('#skF_1'(u1_struct_0(k4_waybel_9(A_452, '#skF_7', '#skF_8')), B_453), u1_struct_0('#skF_7')) | r1_tarski(u1_struct_0(k4_waybel_9(A_452, '#skF_7', '#skF_8')), B_453) | ~l1_waybel_0('#skF_7', A_452) | ~l1_struct_0(A_452) | v2_struct_0(A_452))), inference(negUnitSimplification, [status(thm)], [c_56, c_719])).
% 4.39/1.92  tff(c_8, plain, (![A_6, B_7]: (r2_hidden(A_6, B_7) | v1_xboole_0(B_7) | ~m1_subset_1(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.39/1.92  tff(c_76, plain, (![A_199, B_200]: (~r2_hidden('#skF_1'(A_199, B_200), B_200) | r1_tarski(A_199, B_200))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.39/1.92  tff(c_81, plain, (![A_199, B_7]: (r1_tarski(A_199, B_7) | v1_xboole_0(B_7) | ~m1_subset_1('#skF_1'(A_199, B_7), B_7))), inference(resolution, [status(thm)], [c_8, c_76])).
% 4.39/1.92  tff(c_739, plain, (![A_452]: (v1_xboole_0(u1_struct_0('#skF_7')) | r1_tarski(u1_struct_0(k4_waybel_9(A_452, '#skF_7', '#skF_8')), u1_struct_0('#skF_7')) | ~l1_waybel_0('#skF_7', A_452) | ~l1_struct_0(A_452) | v2_struct_0(A_452))), inference(resolution, [status(thm)], [c_721, c_81])).
% 4.39/1.92  tff(c_744, plain, (v1_xboole_0(u1_struct_0('#skF_7'))), inference(splitLeft, [status(thm)], [c_739])).
% 4.39/1.92  tff(c_14, plain, (![A_12]: (v2_struct_0(A_12) | ~v1_xboole_0(u1_struct_0(A_12)) | ~l1_struct_0(A_12))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.39/1.92  tff(c_747, plain, (v2_struct_0('#skF_7') | ~l1_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_744, c_14])).
% 4.39/1.92  tff(c_750, plain, (~l1_struct_0('#skF_7')), inference(negUnitSimplification, [status(thm)], [c_56, c_747])).
% 4.39/1.92  tff(c_753, plain, (~l1_orders_2('#skF_7')), inference(resolution, [status(thm)], [c_10, c_750])).
% 4.39/1.92  tff(c_757, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_69, c_753])).
% 4.39/1.92  tff(c_789, plain, (![A_461]: (r1_tarski(u1_struct_0(k4_waybel_9(A_461, '#skF_7', '#skF_8')), u1_struct_0('#skF_7')) | ~l1_waybel_0('#skF_7', A_461) | ~l1_struct_0(A_461) | v2_struct_0(A_461))), inference(splitRight, [status(thm)], [c_739])).
% 4.39/1.92  tff(c_50, plain, (~r1_tarski(u1_struct_0(k4_waybel_9('#skF_6', '#skF_7', '#skF_8')), u1_struct_0('#skF_7'))), inference(cnfTransformation, [status(thm)], [f_123])).
% 4.39/1.92  tff(c_806, plain, (~l1_waybel_0('#skF_7', '#skF_6') | ~l1_struct_0('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_789, c_50])).
% 4.39/1.92  tff(c_816, plain, (v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_54, c_806])).
% 4.39/1.92  tff(c_818, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_816])).
% 4.39/1.92  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.39/1.92  
% 4.39/1.92  Inference rules
% 4.39/1.92  ----------------------
% 4.39/1.92  #Ref     : 0
% 4.39/1.92  #Sup     : 165
% 4.39/1.92  #Fact    : 0
% 4.39/1.92  #Define  : 0
% 4.39/1.92  #Split   : 2
% 4.39/1.92  #Chain   : 0
% 4.39/1.92  #Close   : 0
% 4.39/1.92  
% 4.39/1.92  Ordering : KBO
% 4.39/1.92  
% 4.39/1.92  Simplification rules
% 4.39/1.92  ----------------------
% 4.39/1.92  #Subsume      : 21
% 4.39/1.92  #Demod        : 31
% 4.39/1.92  #Tautology    : 21
% 4.39/1.92  #SimpNegUnit  : 39
% 4.39/1.92  #BackRed      : 0
% 4.39/1.92  
% 4.39/1.92  #Partial instantiations: 0
% 4.39/1.92  #Strategies tried      : 1
% 4.39/1.92  
% 4.39/1.92  Timing (in seconds)
% 4.39/1.92  ----------------------
% 4.39/1.92  Preprocessing        : 0.45
% 4.39/1.92  Parsing              : 0.22
% 4.39/1.92  CNF conversion       : 0.04
% 4.39/1.92  Main loop            : 0.64
% 4.39/1.92  Inferencing          : 0.23
% 4.39/1.92  Reduction            : 0.15
% 4.39/1.92  Demodulation         : 0.10
% 4.39/1.92  BG Simplification    : 0.04
% 4.39/1.92  Subsumption          : 0.20
% 4.39/1.93  Abstraction          : 0.04
% 4.39/1.93  MUC search           : 0.00
% 4.39/1.93  Cooper               : 0.00
% 4.39/1.93  Total                : 1.12
% 4.39/1.93  Index Insertion      : 0.00
% 4.39/1.93  Index Deletion       : 0.00
% 4.39/1.93  Index Matching       : 0.00
% 4.39/1.93  BG Taut test         : 0.00
%------------------------------------------------------------------------------
