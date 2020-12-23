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
% DateTime   : Thu Dec  3 10:31:08 EST 2020

% Result     : Theorem 15.23s
% Output     : CNFRefutation 15.23s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 197 expanded)
%              Number of leaves         :   34 (  85 expanded)
%              Depth                    :   20
%              Number of atoms          :  493 ( 925 expanded)
%              Number of equality atoms :   17 (  63 expanded)
%              Maximal formula depth    :   21 (   8 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > r1_orders_2 > v6_waybel_0 > r2_hidden > r1_tarski > m1_subset_1 > l1_waybel_0 > v2_struct_0 > l1_struct_0 > k2_partfun1 > k4_waybel_9 > a_3_0_waybel_9 > u1_waybel_0 > k1_toler_1 > #nlpp > u1_struct_0 > u1_orders_2 > #skF_2 > #skF_7 > #skF_6 > #skF_9 > #skF_4 > #skF_8 > #skF_5 > #skF_3 > #skF_1

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
    '#skF_6': ( $i * $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

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

tff(a_3_0_waybel_9,type,(
    a_3_0_waybel_9: ( $i * $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_127,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & l1_struct_0(A) )
       => ! [B] :
            ( ( ~ v2_struct_0(B)
              & l1_waybel_0(B,A) )
           => ! [C] :
                ( m1_subset_1(C,u1_struct_0(B))
               => u1_struct_0(k4_waybel_9(A,B,C)) = a_3_0_waybel_9(A,B,C) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_waybel_9)).

tff(f_89,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A)
        & ~ v2_struct_0(B)
        & l1_waybel_0(B,A)
        & m1_subset_1(C,u1_struct_0(B)) )
     => ( v6_waybel_0(k4_waybel_9(A,B,C),A)
        & l1_waybel_0(k4_waybel_9(A,B,C),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_waybel_9)).

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_73,axiom,(
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

tff(f_110,axiom,(
    ! [A,B,C,D] :
      ( ( ~ v2_struct_0(B)
        & l1_struct_0(B)
        & ~ v2_struct_0(C)
        & l1_waybel_0(C,B)
        & m1_subset_1(D,u1_struct_0(C)) )
     => ( r2_hidden(A,a_3_0_waybel_9(B,C,D))
      <=> ? [E] :
            ( m1_subset_1(E,u1_struct_0(C))
            & A = E
            & r1_orders_2(C,D,E) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fraenkel_a_3_0_waybel_9)).

tff(c_64,plain,(
    ~ v2_struct_0('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_62,plain,(
    l1_struct_0('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_58,plain,(
    l1_waybel_0('#skF_8','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_60,plain,(
    ~ v2_struct_0('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_56,plain,(
    m1_subset_1('#skF_9',u1_struct_0('#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_99,plain,(
    ! [A_211,B_212,C_213] :
      ( l1_waybel_0(k4_waybel_9(A_211,B_212,C_213),A_211)
      | ~ m1_subset_1(C_213,u1_struct_0(B_212))
      | ~ l1_waybel_0(B_212,A_211)
      | v2_struct_0(B_212)
      | ~ l1_struct_0(A_211)
      | v2_struct_0(A_211) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_101,plain,(
    ! [A_211] :
      ( l1_waybel_0(k4_waybel_9(A_211,'#skF_8','#skF_9'),A_211)
      | ~ l1_waybel_0('#skF_8',A_211)
      | v2_struct_0('#skF_8')
      | ~ l1_struct_0(A_211)
      | v2_struct_0(A_211) ) ),
    inference(resolution,[status(thm)],[c_56,c_99])).

tff(c_104,plain,(
    ! [A_211] :
      ( l1_waybel_0(k4_waybel_9(A_211,'#skF_8','#skF_9'),A_211)
      | ~ l1_waybel_0('#skF_8',A_211)
      | ~ l1_struct_0(A_211)
      | v2_struct_0(A_211) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_101])).

tff(c_44,plain,(
    ! [A_180,B_181,C_182] :
      ( v6_waybel_0(k4_waybel_9(A_180,B_181,C_182),A_180)
      | ~ m1_subset_1(C_182,u1_struct_0(B_181))
      | ~ l1_waybel_0(B_181,A_180)
      | v2_struct_0(B_181)
      | ~ l1_struct_0(A_180)
      | v2_struct_0(A_180) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_12,plain,(
    ! [B_7] : r1_tarski(B_7,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_82,plain,(
    ! [C_201,B_202,A_203] :
      ( r2_hidden(C_201,B_202)
      | ~ r2_hidden(C_201,A_203)
      | ~ r1_tarski(A_203,B_202) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_85,plain,(
    ! [A_1,B_2,B_202] :
      ( r2_hidden('#skF_1'(A_1,B_2),B_202)
      | ~ r1_tarski(A_1,B_202)
      | r1_tarski(A_1,B_2) ) ),
    inference(resolution,[status(thm)],[c_6,c_82])).

tff(c_199,plain,(
    ! [A_276,B_277,C_278,E_279] :
      ( '#skF_2'(A_276,k4_waybel_9(A_276,B_277,C_278),B_277,C_278,E_279) = E_279
      | ~ r2_hidden(E_279,u1_struct_0(k4_waybel_9(A_276,B_277,C_278)))
      | ~ l1_waybel_0(k4_waybel_9(A_276,B_277,C_278),A_276)
      | ~ v6_waybel_0(k4_waybel_9(A_276,B_277,C_278),A_276)
      | ~ m1_subset_1(C_278,u1_struct_0(B_277))
      | ~ l1_waybel_0(B_277,A_276)
      | v2_struct_0(B_277)
      | ~ l1_struct_0(A_276)
      | v2_struct_0(A_276) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_4105,plain,(
    ! [A_574,B_575,C_576,B_577] :
      ( '#skF_2'(A_574,k4_waybel_9(A_574,B_575,C_576),B_575,C_576,'#skF_1'(u1_struct_0(k4_waybel_9(A_574,B_575,C_576)),B_577)) = '#skF_1'(u1_struct_0(k4_waybel_9(A_574,B_575,C_576)),B_577)
      | ~ l1_waybel_0(k4_waybel_9(A_574,B_575,C_576),A_574)
      | ~ v6_waybel_0(k4_waybel_9(A_574,B_575,C_576),A_574)
      | ~ m1_subset_1(C_576,u1_struct_0(B_575))
      | ~ l1_waybel_0(B_575,A_574)
      | v2_struct_0(B_575)
      | ~ l1_struct_0(A_574)
      | v2_struct_0(A_574)
      | r1_tarski(u1_struct_0(k4_waybel_9(A_574,B_575,C_576)),B_577) ) ),
    inference(resolution,[status(thm)],[c_6,c_199])).

tff(c_40,plain,(
    ! [A_8,B_96,C_140,E_173] :
      ( m1_subset_1('#skF_2'(A_8,k4_waybel_9(A_8,B_96,C_140),B_96,C_140,E_173),u1_struct_0(B_96))
      | ~ r2_hidden(E_173,u1_struct_0(k4_waybel_9(A_8,B_96,C_140)))
      | ~ l1_waybel_0(k4_waybel_9(A_8,B_96,C_140),A_8)
      | ~ v6_waybel_0(k4_waybel_9(A_8,B_96,C_140),A_8)
      | ~ m1_subset_1(C_140,u1_struct_0(B_96))
      | ~ l1_waybel_0(B_96,A_8)
      | v2_struct_0(B_96)
      | ~ l1_struct_0(A_8)
      | v2_struct_0(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_14636,plain,(
    ! [A_788,B_789,C_790,B_791] :
      ( m1_subset_1('#skF_1'(u1_struct_0(k4_waybel_9(A_788,B_789,C_790)),B_791),u1_struct_0(B_789))
      | ~ r2_hidden('#skF_1'(u1_struct_0(k4_waybel_9(A_788,B_789,C_790)),B_791),u1_struct_0(k4_waybel_9(A_788,B_789,C_790)))
      | ~ l1_waybel_0(k4_waybel_9(A_788,B_789,C_790),A_788)
      | ~ v6_waybel_0(k4_waybel_9(A_788,B_789,C_790),A_788)
      | ~ m1_subset_1(C_790,u1_struct_0(B_789))
      | ~ l1_waybel_0(B_789,A_788)
      | v2_struct_0(B_789)
      | ~ l1_struct_0(A_788)
      | v2_struct_0(A_788)
      | ~ l1_waybel_0(k4_waybel_9(A_788,B_789,C_790),A_788)
      | ~ v6_waybel_0(k4_waybel_9(A_788,B_789,C_790),A_788)
      | ~ m1_subset_1(C_790,u1_struct_0(B_789))
      | ~ l1_waybel_0(B_789,A_788)
      | v2_struct_0(B_789)
      | ~ l1_struct_0(A_788)
      | v2_struct_0(A_788)
      | r1_tarski(u1_struct_0(k4_waybel_9(A_788,B_789,C_790)),B_791) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4105,c_40])).

tff(c_14648,plain,(
    ! [A_788,B_789,C_790,B_2] :
      ( m1_subset_1('#skF_1'(u1_struct_0(k4_waybel_9(A_788,B_789,C_790)),B_2),u1_struct_0(B_789))
      | ~ l1_waybel_0(k4_waybel_9(A_788,B_789,C_790),A_788)
      | ~ v6_waybel_0(k4_waybel_9(A_788,B_789,C_790),A_788)
      | ~ m1_subset_1(C_790,u1_struct_0(B_789))
      | ~ l1_waybel_0(B_789,A_788)
      | v2_struct_0(B_789)
      | ~ l1_struct_0(A_788)
      | v2_struct_0(A_788)
      | ~ r1_tarski(u1_struct_0(k4_waybel_9(A_788,B_789,C_790)),u1_struct_0(k4_waybel_9(A_788,B_789,C_790)))
      | r1_tarski(u1_struct_0(k4_waybel_9(A_788,B_789,C_790)),B_2) ) ),
    inference(resolution,[status(thm)],[c_85,c_14636])).

tff(c_14662,plain,(
    ! [A_792,B_793,C_794,B_795] :
      ( m1_subset_1('#skF_1'(u1_struct_0(k4_waybel_9(A_792,B_793,C_794)),B_795),u1_struct_0(B_793))
      | ~ l1_waybel_0(k4_waybel_9(A_792,B_793,C_794),A_792)
      | ~ v6_waybel_0(k4_waybel_9(A_792,B_793,C_794),A_792)
      | ~ m1_subset_1(C_794,u1_struct_0(B_793))
      | ~ l1_waybel_0(B_793,A_792)
      | v2_struct_0(B_793)
      | ~ l1_struct_0(A_792)
      | v2_struct_0(A_792)
      | r1_tarski(u1_struct_0(k4_waybel_9(A_792,B_793,C_794)),B_795) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_14648])).

tff(c_14666,plain,(
    ! [A_796,B_797,C_798,B_799] :
      ( m1_subset_1('#skF_1'(u1_struct_0(k4_waybel_9(A_796,B_797,C_798)),B_799),u1_struct_0(B_797))
      | ~ l1_waybel_0(k4_waybel_9(A_796,B_797,C_798),A_796)
      | r1_tarski(u1_struct_0(k4_waybel_9(A_796,B_797,C_798)),B_799)
      | ~ m1_subset_1(C_798,u1_struct_0(B_797))
      | ~ l1_waybel_0(B_797,A_796)
      | v2_struct_0(B_797)
      | ~ l1_struct_0(A_796)
      | v2_struct_0(A_796) ) ),
    inference(resolution,[status(thm)],[c_44,c_14662])).

tff(c_14680,plain,(
    ! [A_211,B_799] :
      ( m1_subset_1('#skF_1'(u1_struct_0(k4_waybel_9(A_211,'#skF_8','#skF_9')),B_799),u1_struct_0('#skF_8'))
      | r1_tarski(u1_struct_0(k4_waybel_9(A_211,'#skF_8','#skF_9')),B_799)
      | ~ m1_subset_1('#skF_9',u1_struct_0('#skF_8'))
      | v2_struct_0('#skF_8')
      | ~ l1_waybel_0('#skF_8',A_211)
      | ~ l1_struct_0(A_211)
      | v2_struct_0(A_211) ) ),
    inference(resolution,[status(thm)],[c_104,c_14666])).

tff(c_14695,plain,(
    ! [A_211,B_799] :
      ( m1_subset_1('#skF_1'(u1_struct_0(k4_waybel_9(A_211,'#skF_8','#skF_9')),B_799),u1_struct_0('#skF_8'))
      | r1_tarski(u1_struct_0(k4_waybel_9(A_211,'#skF_8','#skF_9')),B_799)
      | v2_struct_0('#skF_8')
      | ~ l1_waybel_0('#skF_8',A_211)
      | ~ l1_struct_0(A_211)
      | v2_struct_0(A_211) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_14680])).

tff(c_14697,plain,(
    ! [A_800,B_801] :
      ( m1_subset_1('#skF_1'(u1_struct_0(k4_waybel_9(A_800,'#skF_8','#skF_9')),B_801),u1_struct_0('#skF_8'))
      | r1_tarski(u1_struct_0(k4_waybel_9(A_800,'#skF_8','#skF_9')),B_801)
      | ~ l1_waybel_0('#skF_8',A_800)
      | ~ l1_struct_0(A_800)
      | v2_struct_0(A_800) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_14695])).

tff(c_36,plain,(
    ! [B_96,C_140,A_8,E_173] :
      ( r1_orders_2(B_96,C_140,'#skF_2'(A_8,k4_waybel_9(A_8,B_96,C_140),B_96,C_140,E_173))
      | ~ r2_hidden(E_173,u1_struct_0(k4_waybel_9(A_8,B_96,C_140)))
      | ~ l1_waybel_0(k4_waybel_9(A_8,B_96,C_140),A_8)
      | ~ v6_waybel_0(k4_waybel_9(A_8,B_96,C_140),A_8)
      | ~ m1_subset_1(C_140,u1_struct_0(B_96))
      | ~ l1_waybel_0(B_96,A_8)
      | v2_struct_0(B_96)
      | ~ l1_struct_0(A_8)
      | v2_struct_0(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_13788,plain,(
    ! [B_765,C_766,A_767,B_768] :
      ( r1_orders_2(B_765,C_766,'#skF_1'(u1_struct_0(k4_waybel_9(A_767,B_765,C_766)),B_768))
      | ~ r2_hidden('#skF_1'(u1_struct_0(k4_waybel_9(A_767,B_765,C_766)),B_768),u1_struct_0(k4_waybel_9(A_767,B_765,C_766)))
      | ~ l1_waybel_0(k4_waybel_9(A_767,B_765,C_766),A_767)
      | ~ v6_waybel_0(k4_waybel_9(A_767,B_765,C_766),A_767)
      | ~ m1_subset_1(C_766,u1_struct_0(B_765))
      | ~ l1_waybel_0(B_765,A_767)
      | v2_struct_0(B_765)
      | ~ l1_struct_0(A_767)
      | v2_struct_0(A_767)
      | ~ l1_waybel_0(k4_waybel_9(A_767,B_765,C_766),A_767)
      | ~ v6_waybel_0(k4_waybel_9(A_767,B_765,C_766),A_767)
      | ~ m1_subset_1(C_766,u1_struct_0(B_765))
      | ~ l1_waybel_0(B_765,A_767)
      | v2_struct_0(B_765)
      | ~ l1_struct_0(A_767)
      | v2_struct_0(A_767)
      | r1_tarski(u1_struct_0(k4_waybel_9(A_767,B_765,C_766)),B_768) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4105,c_36])).

tff(c_13800,plain,(
    ! [B_765,C_766,A_767,B_2] :
      ( r1_orders_2(B_765,C_766,'#skF_1'(u1_struct_0(k4_waybel_9(A_767,B_765,C_766)),B_2))
      | ~ l1_waybel_0(k4_waybel_9(A_767,B_765,C_766),A_767)
      | ~ v6_waybel_0(k4_waybel_9(A_767,B_765,C_766),A_767)
      | ~ m1_subset_1(C_766,u1_struct_0(B_765))
      | ~ l1_waybel_0(B_765,A_767)
      | v2_struct_0(B_765)
      | ~ l1_struct_0(A_767)
      | v2_struct_0(A_767)
      | ~ r1_tarski(u1_struct_0(k4_waybel_9(A_767,B_765,C_766)),u1_struct_0(k4_waybel_9(A_767,B_765,C_766)))
      | r1_tarski(u1_struct_0(k4_waybel_9(A_767,B_765,C_766)),B_2) ) ),
    inference(resolution,[status(thm)],[c_85,c_13788])).

tff(c_13814,plain,(
    ! [B_769,C_770,A_771,B_772] :
      ( r1_orders_2(B_769,C_770,'#skF_1'(u1_struct_0(k4_waybel_9(A_771,B_769,C_770)),B_772))
      | ~ l1_waybel_0(k4_waybel_9(A_771,B_769,C_770),A_771)
      | ~ v6_waybel_0(k4_waybel_9(A_771,B_769,C_770),A_771)
      | ~ m1_subset_1(C_770,u1_struct_0(B_769))
      | ~ l1_waybel_0(B_769,A_771)
      | v2_struct_0(B_769)
      | ~ l1_struct_0(A_771)
      | v2_struct_0(A_771)
      | r1_tarski(u1_struct_0(k4_waybel_9(A_771,B_769,C_770)),B_772) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_13800])).

tff(c_13818,plain,(
    ! [B_773,C_774,A_775,B_776] :
      ( r1_orders_2(B_773,C_774,'#skF_1'(u1_struct_0(k4_waybel_9(A_775,B_773,C_774)),B_776))
      | ~ l1_waybel_0(k4_waybel_9(A_775,B_773,C_774),A_775)
      | r1_tarski(u1_struct_0(k4_waybel_9(A_775,B_773,C_774)),B_776)
      | ~ m1_subset_1(C_774,u1_struct_0(B_773))
      | ~ l1_waybel_0(B_773,A_775)
      | v2_struct_0(B_773)
      | ~ l1_struct_0(A_775)
      | v2_struct_0(A_775) ) ),
    inference(resolution,[status(thm)],[c_44,c_13814])).

tff(c_13832,plain,(
    ! [A_211,B_776] :
      ( r1_orders_2('#skF_8','#skF_9','#skF_1'(u1_struct_0(k4_waybel_9(A_211,'#skF_8','#skF_9')),B_776))
      | r1_tarski(u1_struct_0(k4_waybel_9(A_211,'#skF_8','#skF_9')),B_776)
      | ~ m1_subset_1('#skF_9',u1_struct_0('#skF_8'))
      | v2_struct_0('#skF_8')
      | ~ l1_waybel_0('#skF_8',A_211)
      | ~ l1_struct_0(A_211)
      | v2_struct_0(A_211) ) ),
    inference(resolution,[status(thm)],[c_104,c_13818])).

tff(c_13847,plain,(
    ! [A_211,B_776] :
      ( r1_orders_2('#skF_8','#skF_9','#skF_1'(u1_struct_0(k4_waybel_9(A_211,'#skF_8','#skF_9')),B_776))
      | r1_tarski(u1_struct_0(k4_waybel_9(A_211,'#skF_8','#skF_9')),B_776)
      | v2_struct_0('#skF_8')
      | ~ l1_waybel_0('#skF_8',A_211)
      | ~ l1_struct_0(A_211)
      | v2_struct_0(A_211) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_13832])).

tff(c_13849,plain,(
    ! [A_777,B_778] :
      ( r1_orders_2('#skF_8','#skF_9','#skF_1'(u1_struct_0(k4_waybel_9(A_777,'#skF_8','#skF_9')),B_778))
      | r1_tarski(u1_struct_0(k4_waybel_9(A_777,'#skF_8','#skF_9')),B_778)
      | ~ l1_waybel_0('#skF_8',A_777)
      | ~ l1_struct_0(A_777)
      | v2_struct_0(A_777) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_13847])).

tff(c_122,plain,(
    ! [E_226,B_227,C_228,D_229] :
      ( r2_hidden(E_226,a_3_0_waybel_9(B_227,C_228,D_229))
      | ~ r1_orders_2(C_228,D_229,E_226)
      | ~ m1_subset_1(E_226,u1_struct_0(C_228))
      | ~ m1_subset_1(D_229,u1_struct_0(C_228))
      | ~ l1_waybel_0(C_228,B_227)
      | v2_struct_0(C_228)
      | ~ l1_struct_0(B_227)
      | v2_struct_0(B_227) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_134,plain,(
    ! [A_1,B_227,C_228,D_229] :
      ( r1_tarski(A_1,a_3_0_waybel_9(B_227,C_228,D_229))
      | ~ r1_orders_2(C_228,D_229,'#skF_1'(A_1,a_3_0_waybel_9(B_227,C_228,D_229)))
      | ~ m1_subset_1('#skF_1'(A_1,a_3_0_waybel_9(B_227,C_228,D_229)),u1_struct_0(C_228))
      | ~ m1_subset_1(D_229,u1_struct_0(C_228))
      | ~ l1_waybel_0(C_228,B_227)
      | v2_struct_0(C_228)
      | ~ l1_struct_0(B_227)
      | v2_struct_0(B_227) ) ),
    inference(resolution,[status(thm)],[c_122,c_4])).

tff(c_13852,plain,(
    ! [A_777,B_227] :
      ( ~ m1_subset_1('#skF_1'(u1_struct_0(k4_waybel_9(A_777,'#skF_8','#skF_9')),a_3_0_waybel_9(B_227,'#skF_8','#skF_9')),u1_struct_0('#skF_8'))
      | ~ m1_subset_1('#skF_9',u1_struct_0('#skF_8'))
      | ~ l1_waybel_0('#skF_8',B_227)
      | v2_struct_0('#skF_8')
      | ~ l1_struct_0(B_227)
      | v2_struct_0(B_227)
      | r1_tarski(u1_struct_0(k4_waybel_9(A_777,'#skF_8','#skF_9')),a_3_0_waybel_9(B_227,'#skF_8','#skF_9'))
      | ~ l1_waybel_0('#skF_8',A_777)
      | ~ l1_struct_0(A_777)
      | v2_struct_0(A_777) ) ),
    inference(resolution,[status(thm)],[c_13849,c_134])).

tff(c_13857,plain,(
    ! [A_777,B_227] :
      ( ~ m1_subset_1('#skF_1'(u1_struct_0(k4_waybel_9(A_777,'#skF_8','#skF_9')),a_3_0_waybel_9(B_227,'#skF_8','#skF_9')),u1_struct_0('#skF_8'))
      | ~ l1_waybel_0('#skF_8',B_227)
      | v2_struct_0('#skF_8')
      | ~ l1_struct_0(B_227)
      | v2_struct_0(B_227)
      | r1_tarski(u1_struct_0(k4_waybel_9(A_777,'#skF_8','#skF_9')),a_3_0_waybel_9(B_227,'#skF_8','#skF_9'))
      | ~ l1_waybel_0('#skF_8',A_777)
      | ~ l1_struct_0(A_777)
      | v2_struct_0(A_777) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_13852])).

tff(c_13858,plain,(
    ! [A_777,B_227] :
      ( ~ m1_subset_1('#skF_1'(u1_struct_0(k4_waybel_9(A_777,'#skF_8','#skF_9')),a_3_0_waybel_9(B_227,'#skF_8','#skF_9')),u1_struct_0('#skF_8'))
      | ~ l1_waybel_0('#skF_8',B_227)
      | ~ l1_struct_0(B_227)
      | v2_struct_0(B_227)
      | r1_tarski(u1_struct_0(k4_waybel_9(A_777,'#skF_8','#skF_9')),a_3_0_waybel_9(B_227,'#skF_8','#skF_9'))
      | ~ l1_waybel_0('#skF_8',A_777)
      | ~ l1_struct_0(A_777)
      | v2_struct_0(A_777) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_13857])).

tff(c_14769,plain,(
    ! [B_805,A_806] :
      ( ~ l1_waybel_0('#skF_8',B_805)
      | ~ l1_struct_0(B_805)
      | v2_struct_0(B_805)
      | r1_tarski(u1_struct_0(k4_waybel_9(A_806,'#skF_8','#skF_9')),a_3_0_waybel_9(B_805,'#skF_8','#skF_9'))
      | ~ l1_waybel_0('#skF_8',A_806)
      | ~ l1_struct_0(A_806)
      | v2_struct_0(A_806) ) ),
    inference(resolution,[status(thm)],[c_14697,c_13858])).

tff(c_107,plain,(
    ! [A_218,B_219,C_220,D_221] :
      ( '#skF_6'(A_218,B_219,C_220,D_221) = A_218
      | ~ r2_hidden(A_218,a_3_0_waybel_9(B_219,C_220,D_221))
      | ~ m1_subset_1(D_221,u1_struct_0(C_220))
      | ~ l1_waybel_0(C_220,B_219)
      | v2_struct_0(C_220)
      | ~ l1_struct_0(B_219)
      | v2_struct_0(B_219) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_150,plain,(
    ! [B_248,C_249,D_250,B_251] :
      ( '#skF_6'('#skF_1'(a_3_0_waybel_9(B_248,C_249,D_250),B_251),B_248,C_249,D_250) = '#skF_1'(a_3_0_waybel_9(B_248,C_249,D_250),B_251)
      | ~ m1_subset_1(D_250,u1_struct_0(C_249))
      | ~ l1_waybel_0(C_249,B_248)
      | v2_struct_0(C_249)
      | ~ l1_struct_0(B_248)
      | v2_struct_0(B_248)
      | r1_tarski(a_3_0_waybel_9(B_248,C_249,D_250),B_251) ) ),
    inference(resolution,[status(thm)],[c_6,c_107])).

tff(c_48,plain,(
    ! [C_185,D_186,A_183,B_184] :
      ( r1_orders_2(C_185,D_186,'#skF_6'(A_183,B_184,C_185,D_186))
      | ~ r2_hidden(A_183,a_3_0_waybel_9(B_184,C_185,D_186))
      | ~ m1_subset_1(D_186,u1_struct_0(C_185))
      | ~ l1_waybel_0(C_185,B_184)
      | v2_struct_0(C_185)
      | ~ l1_struct_0(B_184)
      | v2_struct_0(B_184) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_539,plain,(
    ! [C_367,D_368,B_369,B_370] :
      ( r1_orders_2(C_367,D_368,'#skF_1'(a_3_0_waybel_9(B_369,C_367,D_368),B_370))
      | ~ r2_hidden('#skF_1'(a_3_0_waybel_9(B_369,C_367,D_368),B_370),a_3_0_waybel_9(B_369,C_367,D_368))
      | ~ m1_subset_1(D_368,u1_struct_0(C_367))
      | ~ l1_waybel_0(C_367,B_369)
      | v2_struct_0(C_367)
      | ~ l1_struct_0(B_369)
      | v2_struct_0(B_369)
      | ~ m1_subset_1(D_368,u1_struct_0(C_367))
      | ~ l1_waybel_0(C_367,B_369)
      | v2_struct_0(C_367)
      | ~ l1_struct_0(B_369)
      | v2_struct_0(B_369)
      | r1_tarski(a_3_0_waybel_9(B_369,C_367,D_368),B_370) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_150,c_48])).

tff(c_578,plain,(
    ! [C_375,D_376,B_377,B_378] :
      ( r1_orders_2(C_375,D_376,'#skF_1'(a_3_0_waybel_9(B_377,C_375,D_376),B_378))
      | ~ m1_subset_1(D_376,u1_struct_0(C_375))
      | ~ l1_waybel_0(C_375,B_377)
      | v2_struct_0(C_375)
      | ~ l1_struct_0(B_377)
      | v2_struct_0(B_377)
      | r1_tarski(a_3_0_waybel_9(B_377,C_375,D_376),B_378) ) ),
    inference(resolution,[status(thm)],[c_6,c_539])).

tff(c_52,plain,(
    ! [A_183,B_184,C_185,D_186] :
      ( m1_subset_1('#skF_6'(A_183,B_184,C_185,D_186),u1_struct_0(C_185))
      | ~ r2_hidden(A_183,a_3_0_waybel_9(B_184,C_185,D_186))
      | ~ m1_subset_1(D_186,u1_struct_0(C_185))
      | ~ l1_waybel_0(C_185,B_184)
      | v2_struct_0(C_185)
      | ~ l1_struct_0(B_184)
      | v2_struct_0(B_184) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_486,plain,(
    ! [B_347,C_348,D_349,B_350] :
      ( m1_subset_1('#skF_1'(a_3_0_waybel_9(B_347,C_348,D_349),B_350),u1_struct_0(C_348))
      | ~ r2_hidden('#skF_1'(a_3_0_waybel_9(B_347,C_348,D_349),B_350),a_3_0_waybel_9(B_347,C_348,D_349))
      | ~ m1_subset_1(D_349,u1_struct_0(C_348))
      | ~ l1_waybel_0(C_348,B_347)
      | v2_struct_0(C_348)
      | ~ l1_struct_0(B_347)
      | v2_struct_0(B_347)
      | ~ m1_subset_1(D_349,u1_struct_0(C_348))
      | ~ l1_waybel_0(C_348,B_347)
      | v2_struct_0(C_348)
      | ~ l1_struct_0(B_347)
      | v2_struct_0(B_347)
      | r1_tarski(a_3_0_waybel_9(B_347,C_348,D_349),B_350) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_150,c_52])).

tff(c_494,plain,(
    ! [B_347,C_348,D_349,B_2] :
      ( m1_subset_1('#skF_1'(a_3_0_waybel_9(B_347,C_348,D_349),B_2),u1_struct_0(C_348))
      | ~ m1_subset_1(D_349,u1_struct_0(C_348))
      | ~ l1_waybel_0(C_348,B_347)
      | v2_struct_0(C_348)
      | ~ l1_struct_0(B_347)
      | v2_struct_0(B_347)
      | ~ r1_tarski(a_3_0_waybel_9(B_347,C_348,D_349),a_3_0_waybel_9(B_347,C_348,D_349))
      | r1_tarski(a_3_0_waybel_9(B_347,C_348,D_349),B_2) ) ),
    inference(resolution,[status(thm)],[c_85,c_486])).

tff(c_504,plain,(
    ! [B_351,C_352,D_353,B_354] :
      ( m1_subset_1('#skF_1'(a_3_0_waybel_9(B_351,C_352,D_353),B_354),u1_struct_0(C_352))
      | ~ m1_subset_1(D_353,u1_struct_0(C_352))
      | ~ l1_waybel_0(C_352,B_351)
      | v2_struct_0(C_352)
      | ~ l1_struct_0(B_351)
      | v2_struct_0(B_351)
      | r1_tarski(a_3_0_waybel_9(B_351,C_352,D_353),B_354) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_494])).

tff(c_165,plain,(
    ! [F_252,A_253,B_254,C_255] :
      ( r2_hidden(F_252,u1_struct_0(k4_waybel_9(A_253,B_254,C_255)))
      | ~ r1_orders_2(B_254,C_255,F_252)
      | ~ m1_subset_1(F_252,u1_struct_0(B_254))
      | ~ l1_waybel_0(k4_waybel_9(A_253,B_254,C_255),A_253)
      | ~ v6_waybel_0(k4_waybel_9(A_253,B_254,C_255),A_253)
      | ~ m1_subset_1(C_255,u1_struct_0(B_254))
      | ~ l1_waybel_0(B_254,A_253)
      | v2_struct_0(B_254)
      | ~ l1_struct_0(A_253)
      | v2_struct_0(A_253) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_169,plain,(
    ! [F_256,A_257,B_258,C_259] :
      ( r2_hidden(F_256,u1_struct_0(k4_waybel_9(A_257,B_258,C_259)))
      | ~ r1_orders_2(B_258,C_259,F_256)
      | ~ m1_subset_1(F_256,u1_struct_0(B_258))
      | ~ l1_waybel_0(k4_waybel_9(A_257,B_258,C_259),A_257)
      | ~ m1_subset_1(C_259,u1_struct_0(B_258))
      | ~ l1_waybel_0(B_258,A_257)
      | v2_struct_0(B_258)
      | ~ l1_struct_0(A_257)
      | v2_struct_0(A_257) ) ),
    inference(resolution,[status(thm)],[c_44,c_165])).

tff(c_171,plain,(
    ! [F_256,A_211] :
      ( r2_hidden(F_256,u1_struct_0(k4_waybel_9(A_211,'#skF_8','#skF_9')))
      | ~ r1_orders_2('#skF_8','#skF_9',F_256)
      | ~ m1_subset_1(F_256,u1_struct_0('#skF_8'))
      | ~ m1_subset_1('#skF_9',u1_struct_0('#skF_8'))
      | v2_struct_0('#skF_8')
      | ~ l1_waybel_0('#skF_8',A_211)
      | ~ l1_struct_0(A_211)
      | v2_struct_0(A_211) ) ),
    inference(resolution,[status(thm)],[c_104,c_169])).

tff(c_174,plain,(
    ! [F_256,A_211] :
      ( r2_hidden(F_256,u1_struct_0(k4_waybel_9(A_211,'#skF_8','#skF_9')))
      | ~ r1_orders_2('#skF_8','#skF_9',F_256)
      | ~ m1_subset_1(F_256,u1_struct_0('#skF_8'))
      | v2_struct_0('#skF_8')
      | ~ l1_waybel_0('#skF_8',A_211)
      | ~ l1_struct_0(A_211)
      | v2_struct_0(A_211) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_171])).

tff(c_176,plain,(
    ! [F_260,A_261] :
      ( r2_hidden(F_260,u1_struct_0(k4_waybel_9(A_261,'#skF_8','#skF_9')))
      | ~ r1_orders_2('#skF_8','#skF_9',F_260)
      | ~ m1_subset_1(F_260,u1_struct_0('#skF_8'))
      | ~ l1_waybel_0('#skF_8',A_261)
      | ~ l1_struct_0(A_261)
      | v2_struct_0(A_261) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_174])).

tff(c_184,plain,(
    ! [A_1,A_261] :
      ( r1_tarski(A_1,u1_struct_0(k4_waybel_9(A_261,'#skF_8','#skF_9')))
      | ~ r1_orders_2('#skF_8','#skF_9','#skF_1'(A_1,u1_struct_0(k4_waybel_9(A_261,'#skF_8','#skF_9'))))
      | ~ m1_subset_1('#skF_1'(A_1,u1_struct_0(k4_waybel_9(A_261,'#skF_8','#skF_9'))),u1_struct_0('#skF_8'))
      | ~ l1_waybel_0('#skF_8',A_261)
      | ~ l1_struct_0(A_261)
      | v2_struct_0(A_261) ) ),
    inference(resolution,[status(thm)],[c_176,c_4])).

tff(c_516,plain,(
    ! [B_351,D_353,A_261] :
      ( ~ r1_orders_2('#skF_8','#skF_9','#skF_1'(a_3_0_waybel_9(B_351,'#skF_8',D_353),u1_struct_0(k4_waybel_9(A_261,'#skF_8','#skF_9'))))
      | ~ l1_waybel_0('#skF_8',A_261)
      | ~ l1_struct_0(A_261)
      | v2_struct_0(A_261)
      | ~ m1_subset_1(D_353,u1_struct_0('#skF_8'))
      | ~ l1_waybel_0('#skF_8',B_351)
      | v2_struct_0('#skF_8')
      | ~ l1_struct_0(B_351)
      | v2_struct_0(B_351)
      | r1_tarski(a_3_0_waybel_9(B_351,'#skF_8',D_353),u1_struct_0(k4_waybel_9(A_261,'#skF_8','#skF_9'))) ) ),
    inference(resolution,[status(thm)],[c_504,c_184])).

tff(c_528,plain,(
    ! [B_351,D_353,A_261] :
      ( ~ r1_orders_2('#skF_8','#skF_9','#skF_1'(a_3_0_waybel_9(B_351,'#skF_8',D_353),u1_struct_0(k4_waybel_9(A_261,'#skF_8','#skF_9'))))
      | ~ l1_waybel_0('#skF_8',A_261)
      | ~ l1_struct_0(A_261)
      | v2_struct_0(A_261)
      | ~ m1_subset_1(D_353,u1_struct_0('#skF_8'))
      | ~ l1_waybel_0('#skF_8',B_351)
      | ~ l1_struct_0(B_351)
      | v2_struct_0(B_351)
      | r1_tarski(a_3_0_waybel_9(B_351,'#skF_8',D_353),u1_struct_0(k4_waybel_9(A_261,'#skF_8','#skF_9'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_516])).

tff(c_582,plain,(
    ! [A_261,B_377] :
      ( ~ l1_waybel_0('#skF_8',A_261)
      | ~ l1_struct_0(A_261)
      | v2_struct_0(A_261)
      | ~ m1_subset_1('#skF_9',u1_struct_0('#skF_8'))
      | ~ l1_waybel_0('#skF_8',B_377)
      | v2_struct_0('#skF_8')
      | ~ l1_struct_0(B_377)
      | v2_struct_0(B_377)
      | r1_tarski(a_3_0_waybel_9(B_377,'#skF_8','#skF_9'),u1_struct_0(k4_waybel_9(A_261,'#skF_8','#skF_9'))) ) ),
    inference(resolution,[status(thm)],[c_578,c_528])).

tff(c_590,plain,(
    ! [A_261,B_377] :
      ( ~ l1_waybel_0('#skF_8',A_261)
      | ~ l1_struct_0(A_261)
      | v2_struct_0(A_261)
      | ~ l1_waybel_0('#skF_8',B_377)
      | v2_struct_0('#skF_8')
      | ~ l1_struct_0(B_377)
      | v2_struct_0(B_377)
      | r1_tarski(a_3_0_waybel_9(B_377,'#skF_8','#skF_9'),u1_struct_0(k4_waybel_9(A_261,'#skF_8','#skF_9'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_582])).

tff(c_594,plain,(
    ! [A_379,B_380] :
      ( ~ l1_waybel_0('#skF_8',A_379)
      | ~ l1_struct_0(A_379)
      | v2_struct_0(A_379)
      | ~ l1_waybel_0('#skF_8',B_380)
      | ~ l1_struct_0(B_380)
      | v2_struct_0(B_380)
      | r1_tarski(a_3_0_waybel_9(B_380,'#skF_8','#skF_9'),u1_struct_0(k4_waybel_9(A_379,'#skF_8','#skF_9'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_590])).

tff(c_8,plain,(
    ! [B_7,A_6] :
      ( B_7 = A_6
      | ~ r1_tarski(B_7,A_6)
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_612,plain,(
    ! [A_379,B_380] :
      ( u1_struct_0(k4_waybel_9(A_379,'#skF_8','#skF_9')) = a_3_0_waybel_9(B_380,'#skF_8','#skF_9')
      | ~ r1_tarski(u1_struct_0(k4_waybel_9(A_379,'#skF_8','#skF_9')),a_3_0_waybel_9(B_380,'#skF_8','#skF_9'))
      | ~ l1_waybel_0('#skF_8',A_379)
      | ~ l1_struct_0(A_379)
      | v2_struct_0(A_379)
      | ~ l1_waybel_0('#skF_8',B_380)
      | ~ l1_struct_0(B_380)
      | v2_struct_0(B_380) ) ),
    inference(resolution,[status(thm)],[c_594,c_8])).

tff(c_14804,plain,(
    ! [A_807,B_808] :
      ( u1_struct_0(k4_waybel_9(A_807,'#skF_8','#skF_9')) = a_3_0_waybel_9(B_808,'#skF_8','#skF_9')
      | ~ l1_waybel_0('#skF_8',B_808)
      | ~ l1_struct_0(B_808)
      | v2_struct_0(B_808)
      | ~ l1_waybel_0('#skF_8',A_807)
      | ~ l1_struct_0(A_807)
      | v2_struct_0(A_807) ) ),
    inference(resolution,[status(thm)],[c_14769,c_612])).

tff(c_14806,plain,(
    ! [A_807] :
      ( u1_struct_0(k4_waybel_9(A_807,'#skF_8','#skF_9')) = a_3_0_waybel_9('#skF_7','#skF_8','#skF_9')
      | ~ l1_struct_0('#skF_7')
      | v2_struct_0('#skF_7')
      | ~ l1_waybel_0('#skF_8',A_807)
      | ~ l1_struct_0(A_807)
      | v2_struct_0(A_807) ) ),
    inference(resolution,[status(thm)],[c_58,c_14804])).

tff(c_14809,plain,(
    ! [A_807] :
      ( u1_struct_0(k4_waybel_9(A_807,'#skF_8','#skF_9')) = a_3_0_waybel_9('#skF_7','#skF_8','#skF_9')
      | v2_struct_0('#skF_7')
      | ~ l1_waybel_0('#skF_8',A_807)
      | ~ l1_struct_0(A_807)
      | v2_struct_0(A_807) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_14806])).

tff(c_14811,plain,(
    ! [A_809] :
      ( u1_struct_0(k4_waybel_9(A_809,'#skF_8','#skF_9')) = a_3_0_waybel_9('#skF_7','#skF_8','#skF_9')
      | ~ l1_waybel_0('#skF_8',A_809)
      | ~ l1_struct_0(A_809)
      | v2_struct_0(A_809) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_14809])).

tff(c_54,plain,(
    u1_struct_0(k4_waybel_9('#skF_7','#skF_8','#skF_9')) != a_3_0_waybel_9('#skF_7','#skF_8','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_14934,plain,
    ( ~ l1_waybel_0('#skF_8','#skF_7')
    | ~ l1_struct_0('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_14811,c_54])).

tff(c_14974,plain,(
    v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_58,c_14934])).

tff(c_14976,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_14974])).
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
% 0.13/0.34  % DateTime   : Tue Dec  1 18:10:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 15.23/6.95  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.23/6.96  
% 15.23/6.96  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.23/6.96  %$ r2_relset_1 > r1_orders_2 > v6_waybel_0 > r2_hidden > r1_tarski > m1_subset_1 > l1_waybel_0 > v2_struct_0 > l1_struct_0 > k2_partfun1 > k4_waybel_9 > a_3_0_waybel_9 > u1_waybel_0 > k1_toler_1 > #nlpp > u1_struct_0 > u1_orders_2 > #skF_2 > #skF_7 > #skF_6 > #skF_9 > #skF_4 > #skF_8 > #skF_5 > #skF_3 > #skF_1
% 15.23/6.96  
% 15.23/6.96  %Foreground sorts:
% 15.23/6.96  
% 15.23/6.96  
% 15.23/6.96  %Background operators:
% 15.23/6.96  
% 15.23/6.96  
% 15.23/6.96  %Foreground operators:
% 15.23/6.96  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 15.23/6.96  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 15.23/6.96  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 15.23/6.96  tff(v6_waybel_0, type, v6_waybel_0: ($i * $i) > $o).
% 15.23/6.96  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 15.23/6.96  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i * $i) > $i).
% 15.23/6.96  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 15.23/6.96  tff(k4_waybel_9, type, k4_waybel_9: ($i * $i * $i) > $i).
% 15.23/6.96  tff(k1_toler_1, type, k1_toler_1: ($i * $i) > $i).
% 15.23/6.96  tff('#skF_7', type, '#skF_7': $i).
% 15.23/6.96  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 15.23/6.96  tff('#skF_6', type, '#skF_6': ($i * $i * $i * $i) > $i).
% 15.23/6.96  tff('#skF_9', type, '#skF_9': $i).
% 15.23/6.96  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 15.23/6.96  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 15.23/6.96  tff(u1_waybel_0, type, u1_waybel_0: ($i * $i) > $i).
% 15.23/6.96  tff('#skF_8', type, '#skF_8': $i).
% 15.23/6.96  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 15.23/6.96  tff(l1_waybel_0, type, l1_waybel_0: ($i * $i) > $o).
% 15.23/6.96  tff('#skF_5', type, '#skF_5': ($i * $i * $i * $i) > $i).
% 15.23/6.96  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 15.23/6.96  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 15.23/6.96  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 15.23/6.96  tff(u1_orders_2, type, u1_orders_2: $i > $i).
% 15.23/6.96  tff(a_3_0_waybel_9, type, a_3_0_waybel_9: ($i * $i * $i) > $i).
% 15.23/6.96  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 15.23/6.96  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 15.23/6.96  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 15.23/6.96  
% 15.23/6.98  tff(f_127, negated_conjecture, ~(![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: ((~v2_struct_0(B) & l1_waybel_0(B, A)) => (![C]: (m1_subset_1(C, u1_struct_0(B)) => (u1_struct_0(k4_waybel_9(A, B, C)) = a_3_0_waybel_9(A, B, C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_waybel_9)).
% 15.23/6.98  tff(f_89, axiom, (![A, B, C]: (((((~v2_struct_0(A) & l1_struct_0(A)) & ~v2_struct_0(B)) & l1_waybel_0(B, A)) & m1_subset_1(C, u1_struct_0(B))) => (v6_waybel_0(k4_waybel_9(A, B, C), A) & l1_waybel_0(k4_waybel_9(A, B, C), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k4_waybel_9)).
% 15.23/6.98  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 15.23/6.98  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 15.23/6.98  tff(f_73, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: ((~v2_struct_0(B) & l1_waybel_0(B, A)) => (![C]: (m1_subset_1(C, u1_struct_0(B)) => (![D]: ((v6_waybel_0(D, A) & l1_waybel_0(D, A)) => ((D = k4_waybel_9(A, B, C)) <=> (((![E]: (r2_hidden(E, u1_struct_0(D)) <=> (?[F]: ((m1_subset_1(F, u1_struct_0(B)) & (F = E)) & r1_orders_2(B, C, F))))) & r2_relset_1(u1_struct_0(D), u1_struct_0(D), u1_orders_2(D), k1_toler_1(u1_orders_2(B), u1_struct_0(D)))) & (u1_waybel_0(A, D) = k2_partfun1(u1_struct_0(B), u1_struct_0(A), u1_waybel_0(A, B), u1_struct_0(D))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_waybel_9)).
% 15.23/6.98  tff(f_110, axiom, (![A, B, C, D]: (((((~v2_struct_0(B) & l1_struct_0(B)) & ~v2_struct_0(C)) & l1_waybel_0(C, B)) & m1_subset_1(D, u1_struct_0(C))) => (r2_hidden(A, a_3_0_waybel_9(B, C, D)) <=> (?[E]: ((m1_subset_1(E, u1_struct_0(C)) & (A = E)) & r1_orders_2(C, D, E)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fraenkel_a_3_0_waybel_9)).
% 15.23/6.98  tff(c_64, plain, (~v2_struct_0('#skF_7')), inference(cnfTransformation, [status(thm)], [f_127])).
% 15.23/6.98  tff(c_62, plain, (l1_struct_0('#skF_7')), inference(cnfTransformation, [status(thm)], [f_127])).
% 15.23/6.98  tff(c_58, plain, (l1_waybel_0('#skF_8', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_127])).
% 15.23/6.98  tff(c_60, plain, (~v2_struct_0('#skF_8')), inference(cnfTransformation, [status(thm)], [f_127])).
% 15.23/6.98  tff(c_56, plain, (m1_subset_1('#skF_9', u1_struct_0('#skF_8'))), inference(cnfTransformation, [status(thm)], [f_127])).
% 15.23/6.98  tff(c_99, plain, (![A_211, B_212, C_213]: (l1_waybel_0(k4_waybel_9(A_211, B_212, C_213), A_211) | ~m1_subset_1(C_213, u1_struct_0(B_212)) | ~l1_waybel_0(B_212, A_211) | v2_struct_0(B_212) | ~l1_struct_0(A_211) | v2_struct_0(A_211))), inference(cnfTransformation, [status(thm)], [f_89])).
% 15.23/6.98  tff(c_101, plain, (![A_211]: (l1_waybel_0(k4_waybel_9(A_211, '#skF_8', '#skF_9'), A_211) | ~l1_waybel_0('#skF_8', A_211) | v2_struct_0('#skF_8') | ~l1_struct_0(A_211) | v2_struct_0(A_211))), inference(resolution, [status(thm)], [c_56, c_99])).
% 15.23/6.98  tff(c_104, plain, (![A_211]: (l1_waybel_0(k4_waybel_9(A_211, '#skF_8', '#skF_9'), A_211) | ~l1_waybel_0('#skF_8', A_211) | ~l1_struct_0(A_211) | v2_struct_0(A_211))), inference(negUnitSimplification, [status(thm)], [c_60, c_101])).
% 15.23/6.98  tff(c_44, plain, (![A_180, B_181, C_182]: (v6_waybel_0(k4_waybel_9(A_180, B_181, C_182), A_180) | ~m1_subset_1(C_182, u1_struct_0(B_181)) | ~l1_waybel_0(B_181, A_180) | v2_struct_0(B_181) | ~l1_struct_0(A_180) | v2_struct_0(A_180))), inference(cnfTransformation, [status(thm)], [f_89])).
% 15.23/6.98  tff(c_12, plain, (![B_7]: (r1_tarski(B_7, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 15.23/6.98  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 15.23/6.98  tff(c_82, plain, (![C_201, B_202, A_203]: (r2_hidden(C_201, B_202) | ~r2_hidden(C_201, A_203) | ~r1_tarski(A_203, B_202))), inference(cnfTransformation, [status(thm)], [f_32])).
% 15.23/6.98  tff(c_85, plain, (![A_1, B_2, B_202]: (r2_hidden('#skF_1'(A_1, B_2), B_202) | ~r1_tarski(A_1, B_202) | r1_tarski(A_1, B_2))), inference(resolution, [status(thm)], [c_6, c_82])).
% 15.23/6.98  tff(c_199, plain, (![A_276, B_277, C_278, E_279]: ('#skF_2'(A_276, k4_waybel_9(A_276, B_277, C_278), B_277, C_278, E_279)=E_279 | ~r2_hidden(E_279, u1_struct_0(k4_waybel_9(A_276, B_277, C_278))) | ~l1_waybel_0(k4_waybel_9(A_276, B_277, C_278), A_276) | ~v6_waybel_0(k4_waybel_9(A_276, B_277, C_278), A_276) | ~m1_subset_1(C_278, u1_struct_0(B_277)) | ~l1_waybel_0(B_277, A_276) | v2_struct_0(B_277) | ~l1_struct_0(A_276) | v2_struct_0(A_276))), inference(cnfTransformation, [status(thm)], [f_73])).
% 15.23/6.98  tff(c_4105, plain, (![A_574, B_575, C_576, B_577]: ('#skF_2'(A_574, k4_waybel_9(A_574, B_575, C_576), B_575, C_576, '#skF_1'(u1_struct_0(k4_waybel_9(A_574, B_575, C_576)), B_577))='#skF_1'(u1_struct_0(k4_waybel_9(A_574, B_575, C_576)), B_577) | ~l1_waybel_0(k4_waybel_9(A_574, B_575, C_576), A_574) | ~v6_waybel_0(k4_waybel_9(A_574, B_575, C_576), A_574) | ~m1_subset_1(C_576, u1_struct_0(B_575)) | ~l1_waybel_0(B_575, A_574) | v2_struct_0(B_575) | ~l1_struct_0(A_574) | v2_struct_0(A_574) | r1_tarski(u1_struct_0(k4_waybel_9(A_574, B_575, C_576)), B_577))), inference(resolution, [status(thm)], [c_6, c_199])).
% 15.23/6.98  tff(c_40, plain, (![A_8, B_96, C_140, E_173]: (m1_subset_1('#skF_2'(A_8, k4_waybel_9(A_8, B_96, C_140), B_96, C_140, E_173), u1_struct_0(B_96)) | ~r2_hidden(E_173, u1_struct_0(k4_waybel_9(A_8, B_96, C_140))) | ~l1_waybel_0(k4_waybel_9(A_8, B_96, C_140), A_8) | ~v6_waybel_0(k4_waybel_9(A_8, B_96, C_140), A_8) | ~m1_subset_1(C_140, u1_struct_0(B_96)) | ~l1_waybel_0(B_96, A_8) | v2_struct_0(B_96) | ~l1_struct_0(A_8) | v2_struct_0(A_8))), inference(cnfTransformation, [status(thm)], [f_73])).
% 15.23/6.98  tff(c_14636, plain, (![A_788, B_789, C_790, B_791]: (m1_subset_1('#skF_1'(u1_struct_0(k4_waybel_9(A_788, B_789, C_790)), B_791), u1_struct_0(B_789)) | ~r2_hidden('#skF_1'(u1_struct_0(k4_waybel_9(A_788, B_789, C_790)), B_791), u1_struct_0(k4_waybel_9(A_788, B_789, C_790))) | ~l1_waybel_0(k4_waybel_9(A_788, B_789, C_790), A_788) | ~v6_waybel_0(k4_waybel_9(A_788, B_789, C_790), A_788) | ~m1_subset_1(C_790, u1_struct_0(B_789)) | ~l1_waybel_0(B_789, A_788) | v2_struct_0(B_789) | ~l1_struct_0(A_788) | v2_struct_0(A_788) | ~l1_waybel_0(k4_waybel_9(A_788, B_789, C_790), A_788) | ~v6_waybel_0(k4_waybel_9(A_788, B_789, C_790), A_788) | ~m1_subset_1(C_790, u1_struct_0(B_789)) | ~l1_waybel_0(B_789, A_788) | v2_struct_0(B_789) | ~l1_struct_0(A_788) | v2_struct_0(A_788) | r1_tarski(u1_struct_0(k4_waybel_9(A_788, B_789, C_790)), B_791))), inference(superposition, [status(thm), theory('equality')], [c_4105, c_40])).
% 15.23/6.98  tff(c_14648, plain, (![A_788, B_789, C_790, B_2]: (m1_subset_1('#skF_1'(u1_struct_0(k4_waybel_9(A_788, B_789, C_790)), B_2), u1_struct_0(B_789)) | ~l1_waybel_0(k4_waybel_9(A_788, B_789, C_790), A_788) | ~v6_waybel_0(k4_waybel_9(A_788, B_789, C_790), A_788) | ~m1_subset_1(C_790, u1_struct_0(B_789)) | ~l1_waybel_0(B_789, A_788) | v2_struct_0(B_789) | ~l1_struct_0(A_788) | v2_struct_0(A_788) | ~r1_tarski(u1_struct_0(k4_waybel_9(A_788, B_789, C_790)), u1_struct_0(k4_waybel_9(A_788, B_789, C_790))) | r1_tarski(u1_struct_0(k4_waybel_9(A_788, B_789, C_790)), B_2))), inference(resolution, [status(thm)], [c_85, c_14636])).
% 15.23/6.98  tff(c_14662, plain, (![A_792, B_793, C_794, B_795]: (m1_subset_1('#skF_1'(u1_struct_0(k4_waybel_9(A_792, B_793, C_794)), B_795), u1_struct_0(B_793)) | ~l1_waybel_0(k4_waybel_9(A_792, B_793, C_794), A_792) | ~v6_waybel_0(k4_waybel_9(A_792, B_793, C_794), A_792) | ~m1_subset_1(C_794, u1_struct_0(B_793)) | ~l1_waybel_0(B_793, A_792) | v2_struct_0(B_793) | ~l1_struct_0(A_792) | v2_struct_0(A_792) | r1_tarski(u1_struct_0(k4_waybel_9(A_792, B_793, C_794)), B_795))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_14648])).
% 15.23/6.98  tff(c_14666, plain, (![A_796, B_797, C_798, B_799]: (m1_subset_1('#skF_1'(u1_struct_0(k4_waybel_9(A_796, B_797, C_798)), B_799), u1_struct_0(B_797)) | ~l1_waybel_0(k4_waybel_9(A_796, B_797, C_798), A_796) | r1_tarski(u1_struct_0(k4_waybel_9(A_796, B_797, C_798)), B_799) | ~m1_subset_1(C_798, u1_struct_0(B_797)) | ~l1_waybel_0(B_797, A_796) | v2_struct_0(B_797) | ~l1_struct_0(A_796) | v2_struct_0(A_796))), inference(resolution, [status(thm)], [c_44, c_14662])).
% 15.23/6.98  tff(c_14680, plain, (![A_211, B_799]: (m1_subset_1('#skF_1'(u1_struct_0(k4_waybel_9(A_211, '#skF_8', '#skF_9')), B_799), u1_struct_0('#skF_8')) | r1_tarski(u1_struct_0(k4_waybel_9(A_211, '#skF_8', '#skF_9')), B_799) | ~m1_subset_1('#skF_9', u1_struct_0('#skF_8')) | v2_struct_0('#skF_8') | ~l1_waybel_0('#skF_8', A_211) | ~l1_struct_0(A_211) | v2_struct_0(A_211))), inference(resolution, [status(thm)], [c_104, c_14666])).
% 15.23/6.98  tff(c_14695, plain, (![A_211, B_799]: (m1_subset_1('#skF_1'(u1_struct_0(k4_waybel_9(A_211, '#skF_8', '#skF_9')), B_799), u1_struct_0('#skF_8')) | r1_tarski(u1_struct_0(k4_waybel_9(A_211, '#skF_8', '#skF_9')), B_799) | v2_struct_0('#skF_8') | ~l1_waybel_0('#skF_8', A_211) | ~l1_struct_0(A_211) | v2_struct_0(A_211))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_14680])).
% 15.23/6.98  tff(c_14697, plain, (![A_800, B_801]: (m1_subset_1('#skF_1'(u1_struct_0(k4_waybel_9(A_800, '#skF_8', '#skF_9')), B_801), u1_struct_0('#skF_8')) | r1_tarski(u1_struct_0(k4_waybel_9(A_800, '#skF_8', '#skF_9')), B_801) | ~l1_waybel_0('#skF_8', A_800) | ~l1_struct_0(A_800) | v2_struct_0(A_800))), inference(negUnitSimplification, [status(thm)], [c_60, c_14695])).
% 15.23/6.98  tff(c_36, plain, (![B_96, C_140, A_8, E_173]: (r1_orders_2(B_96, C_140, '#skF_2'(A_8, k4_waybel_9(A_8, B_96, C_140), B_96, C_140, E_173)) | ~r2_hidden(E_173, u1_struct_0(k4_waybel_9(A_8, B_96, C_140))) | ~l1_waybel_0(k4_waybel_9(A_8, B_96, C_140), A_8) | ~v6_waybel_0(k4_waybel_9(A_8, B_96, C_140), A_8) | ~m1_subset_1(C_140, u1_struct_0(B_96)) | ~l1_waybel_0(B_96, A_8) | v2_struct_0(B_96) | ~l1_struct_0(A_8) | v2_struct_0(A_8))), inference(cnfTransformation, [status(thm)], [f_73])).
% 15.23/6.98  tff(c_13788, plain, (![B_765, C_766, A_767, B_768]: (r1_orders_2(B_765, C_766, '#skF_1'(u1_struct_0(k4_waybel_9(A_767, B_765, C_766)), B_768)) | ~r2_hidden('#skF_1'(u1_struct_0(k4_waybel_9(A_767, B_765, C_766)), B_768), u1_struct_0(k4_waybel_9(A_767, B_765, C_766))) | ~l1_waybel_0(k4_waybel_9(A_767, B_765, C_766), A_767) | ~v6_waybel_0(k4_waybel_9(A_767, B_765, C_766), A_767) | ~m1_subset_1(C_766, u1_struct_0(B_765)) | ~l1_waybel_0(B_765, A_767) | v2_struct_0(B_765) | ~l1_struct_0(A_767) | v2_struct_0(A_767) | ~l1_waybel_0(k4_waybel_9(A_767, B_765, C_766), A_767) | ~v6_waybel_0(k4_waybel_9(A_767, B_765, C_766), A_767) | ~m1_subset_1(C_766, u1_struct_0(B_765)) | ~l1_waybel_0(B_765, A_767) | v2_struct_0(B_765) | ~l1_struct_0(A_767) | v2_struct_0(A_767) | r1_tarski(u1_struct_0(k4_waybel_9(A_767, B_765, C_766)), B_768))), inference(superposition, [status(thm), theory('equality')], [c_4105, c_36])).
% 15.23/6.98  tff(c_13800, plain, (![B_765, C_766, A_767, B_2]: (r1_orders_2(B_765, C_766, '#skF_1'(u1_struct_0(k4_waybel_9(A_767, B_765, C_766)), B_2)) | ~l1_waybel_0(k4_waybel_9(A_767, B_765, C_766), A_767) | ~v6_waybel_0(k4_waybel_9(A_767, B_765, C_766), A_767) | ~m1_subset_1(C_766, u1_struct_0(B_765)) | ~l1_waybel_0(B_765, A_767) | v2_struct_0(B_765) | ~l1_struct_0(A_767) | v2_struct_0(A_767) | ~r1_tarski(u1_struct_0(k4_waybel_9(A_767, B_765, C_766)), u1_struct_0(k4_waybel_9(A_767, B_765, C_766))) | r1_tarski(u1_struct_0(k4_waybel_9(A_767, B_765, C_766)), B_2))), inference(resolution, [status(thm)], [c_85, c_13788])).
% 15.23/6.98  tff(c_13814, plain, (![B_769, C_770, A_771, B_772]: (r1_orders_2(B_769, C_770, '#skF_1'(u1_struct_0(k4_waybel_9(A_771, B_769, C_770)), B_772)) | ~l1_waybel_0(k4_waybel_9(A_771, B_769, C_770), A_771) | ~v6_waybel_0(k4_waybel_9(A_771, B_769, C_770), A_771) | ~m1_subset_1(C_770, u1_struct_0(B_769)) | ~l1_waybel_0(B_769, A_771) | v2_struct_0(B_769) | ~l1_struct_0(A_771) | v2_struct_0(A_771) | r1_tarski(u1_struct_0(k4_waybel_9(A_771, B_769, C_770)), B_772))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_13800])).
% 15.23/6.98  tff(c_13818, plain, (![B_773, C_774, A_775, B_776]: (r1_orders_2(B_773, C_774, '#skF_1'(u1_struct_0(k4_waybel_9(A_775, B_773, C_774)), B_776)) | ~l1_waybel_0(k4_waybel_9(A_775, B_773, C_774), A_775) | r1_tarski(u1_struct_0(k4_waybel_9(A_775, B_773, C_774)), B_776) | ~m1_subset_1(C_774, u1_struct_0(B_773)) | ~l1_waybel_0(B_773, A_775) | v2_struct_0(B_773) | ~l1_struct_0(A_775) | v2_struct_0(A_775))), inference(resolution, [status(thm)], [c_44, c_13814])).
% 15.23/6.98  tff(c_13832, plain, (![A_211, B_776]: (r1_orders_2('#skF_8', '#skF_9', '#skF_1'(u1_struct_0(k4_waybel_9(A_211, '#skF_8', '#skF_9')), B_776)) | r1_tarski(u1_struct_0(k4_waybel_9(A_211, '#skF_8', '#skF_9')), B_776) | ~m1_subset_1('#skF_9', u1_struct_0('#skF_8')) | v2_struct_0('#skF_8') | ~l1_waybel_0('#skF_8', A_211) | ~l1_struct_0(A_211) | v2_struct_0(A_211))), inference(resolution, [status(thm)], [c_104, c_13818])).
% 15.23/6.98  tff(c_13847, plain, (![A_211, B_776]: (r1_orders_2('#skF_8', '#skF_9', '#skF_1'(u1_struct_0(k4_waybel_9(A_211, '#skF_8', '#skF_9')), B_776)) | r1_tarski(u1_struct_0(k4_waybel_9(A_211, '#skF_8', '#skF_9')), B_776) | v2_struct_0('#skF_8') | ~l1_waybel_0('#skF_8', A_211) | ~l1_struct_0(A_211) | v2_struct_0(A_211))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_13832])).
% 15.23/6.98  tff(c_13849, plain, (![A_777, B_778]: (r1_orders_2('#skF_8', '#skF_9', '#skF_1'(u1_struct_0(k4_waybel_9(A_777, '#skF_8', '#skF_9')), B_778)) | r1_tarski(u1_struct_0(k4_waybel_9(A_777, '#skF_8', '#skF_9')), B_778) | ~l1_waybel_0('#skF_8', A_777) | ~l1_struct_0(A_777) | v2_struct_0(A_777))), inference(negUnitSimplification, [status(thm)], [c_60, c_13847])).
% 15.23/6.98  tff(c_122, plain, (![E_226, B_227, C_228, D_229]: (r2_hidden(E_226, a_3_0_waybel_9(B_227, C_228, D_229)) | ~r1_orders_2(C_228, D_229, E_226) | ~m1_subset_1(E_226, u1_struct_0(C_228)) | ~m1_subset_1(D_229, u1_struct_0(C_228)) | ~l1_waybel_0(C_228, B_227) | v2_struct_0(C_228) | ~l1_struct_0(B_227) | v2_struct_0(B_227))), inference(cnfTransformation, [status(thm)], [f_110])).
% 15.23/6.98  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 15.23/6.98  tff(c_134, plain, (![A_1, B_227, C_228, D_229]: (r1_tarski(A_1, a_3_0_waybel_9(B_227, C_228, D_229)) | ~r1_orders_2(C_228, D_229, '#skF_1'(A_1, a_3_0_waybel_9(B_227, C_228, D_229))) | ~m1_subset_1('#skF_1'(A_1, a_3_0_waybel_9(B_227, C_228, D_229)), u1_struct_0(C_228)) | ~m1_subset_1(D_229, u1_struct_0(C_228)) | ~l1_waybel_0(C_228, B_227) | v2_struct_0(C_228) | ~l1_struct_0(B_227) | v2_struct_0(B_227))), inference(resolution, [status(thm)], [c_122, c_4])).
% 15.23/6.98  tff(c_13852, plain, (![A_777, B_227]: (~m1_subset_1('#skF_1'(u1_struct_0(k4_waybel_9(A_777, '#skF_8', '#skF_9')), a_3_0_waybel_9(B_227, '#skF_8', '#skF_9')), u1_struct_0('#skF_8')) | ~m1_subset_1('#skF_9', u1_struct_0('#skF_8')) | ~l1_waybel_0('#skF_8', B_227) | v2_struct_0('#skF_8') | ~l1_struct_0(B_227) | v2_struct_0(B_227) | r1_tarski(u1_struct_0(k4_waybel_9(A_777, '#skF_8', '#skF_9')), a_3_0_waybel_9(B_227, '#skF_8', '#skF_9')) | ~l1_waybel_0('#skF_8', A_777) | ~l1_struct_0(A_777) | v2_struct_0(A_777))), inference(resolution, [status(thm)], [c_13849, c_134])).
% 15.23/6.98  tff(c_13857, plain, (![A_777, B_227]: (~m1_subset_1('#skF_1'(u1_struct_0(k4_waybel_9(A_777, '#skF_8', '#skF_9')), a_3_0_waybel_9(B_227, '#skF_8', '#skF_9')), u1_struct_0('#skF_8')) | ~l1_waybel_0('#skF_8', B_227) | v2_struct_0('#skF_8') | ~l1_struct_0(B_227) | v2_struct_0(B_227) | r1_tarski(u1_struct_0(k4_waybel_9(A_777, '#skF_8', '#skF_9')), a_3_0_waybel_9(B_227, '#skF_8', '#skF_9')) | ~l1_waybel_0('#skF_8', A_777) | ~l1_struct_0(A_777) | v2_struct_0(A_777))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_13852])).
% 15.23/6.98  tff(c_13858, plain, (![A_777, B_227]: (~m1_subset_1('#skF_1'(u1_struct_0(k4_waybel_9(A_777, '#skF_8', '#skF_9')), a_3_0_waybel_9(B_227, '#skF_8', '#skF_9')), u1_struct_0('#skF_8')) | ~l1_waybel_0('#skF_8', B_227) | ~l1_struct_0(B_227) | v2_struct_0(B_227) | r1_tarski(u1_struct_0(k4_waybel_9(A_777, '#skF_8', '#skF_9')), a_3_0_waybel_9(B_227, '#skF_8', '#skF_9')) | ~l1_waybel_0('#skF_8', A_777) | ~l1_struct_0(A_777) | v2_struct_0(A_777))), inference(negUnitSimplification, [status(thm)], [c_60, c_13857])).
% 15.23/6.98  tff(c_14769, plain, (![B_805, A_806]: (~l1_waybel_0('#skF_8', B_805) | ~l1_struct_0(B_805) | v2_struct_0(B_805) | r1_tarski(u1_struct_0(k4_waybel_9(A_806, '#skF_8', '#skF_9')), a_3_0_waybel_9(B_805, '#skF_8', '#skF_9')) | ~l1_waybel_0('#skF_8', A_806) | ~l1_struct_0(A_806) | v2_struct_0(A_806))), inference(resolution, [status(thm)], [c_14697, c_13858])).
% 15.23/6.98  tff(c_107, plain, (![A_218, B_219, C_220, D_221]: ('#skF_6'(A_218, B_219, C_220, D_221)=A_218 | ~r2_hidden(A_218, a_3_0_waybel_9(B_219, C_220, D_221)) | ~m1_subset_1(D_221, u1_struct_0(C_220)) | ~l1_waybel_0(C_220, B_219) | v2_struct_0(C_220) | ~l1_struct_0(B_219) | v2_struct_0(B_219))), inference(cnfTransformation, [status(thm)], [f_110])).
% 15.23/6.98  tff(c_150, plain, (![B_248, C_249, D_250, B_251]: ('#skF_6'('#skF_1'(a_3_0_waybel_9(B_248, C_249, D_250), B_251), B_248, C_249, D_250)='#skF_1'(a_3_0_waybel_9(B_248, C_249, D_250), B_251) | ~m1_subset_1(D_250, u1_struct_0(C_249)) | ~l1_waybel_0(C_249, B_248) | v2_struct_0(C_249) | ~l1_struct_0(B_248) | v2_struct_0(B_248) | r1_tarski(a_3_0_waybel_9(B_248, C_249, D_250), B_251))), inference(resolution, [status(thm)], [c_6, c_107])).
% 15.23/6.98  tff(c_48, plain, (![C_185, D_186, A_183, B_184]: (r1_orders_2(C_185, D_186, '#skF_6'(A_183, B_184, C_185, D_186)) | ~r2_hidden(A_183, a_3_0_waybel_9(B_184, C_185, D_186)) | ~m1_subset_1(D_186, u1_struct_0(C_185)) | ~l1_waybel_0(C_185, B_184) | v2_struct_0(C_185) | ~l1_struct_0(B_184) | v2_struct_0(B_184))), inference(cnfTransformation, [status(thm)], [f_110])).
% 15.23/6.98  tff(c_539, plain, (![C_367, D_368, B_369, B_370]: (r1_orders_2(C_367, D_368, '#skF_1'(a_3_0_waybel_9(B_369, C_367, D_368), B_370)) | ~r2_hidden('#skF_1'(a_3_0_waybel_9(B_369, C_367, D_368), B_370), a_3_0_waybel_9(B_369, C_367, D_368)) | ~m1_subset_1(D_368, u1_struct_0(C_367)) | ~l1_waybel_0(C_367, B_369) | v2_struct_0(C_367) | ~l1_struct_0(B_369) | v2_struct_0(B_369) | ~m1_subset_1(D_368, u1_struct_0(C_367)) | ~l1_waybel_0(C_367, B_369) | v2_struct_0(C_367) | ~l1_struct_0(B_369) | v2_struct_0(B_369) | r1_tarski(a_3_0_waybel_9(B_369, C_367, D_368), B_370))), inference(superposition, [status(thm), theory('equality')], [c_150, c_48])).
% 15.23/6.98  tff(c_578, plain, (![C_375, D_376, B_377, B_378]: (r1_orders_2(C_375, D_376, '#skF_1'(a_3_0_waybel_9(B_377, C_375, D_376), B_378)) | ~m1_subset_1(D_376, u1_struct_0(C_375)) | ~l1_waybel_0(C_375, B_377) | v2_struct_0(C_375) | ~l1_struct_0(B_377) | v2_struct_0(B_377) | r1_tarski(a_3_0_waybel_9(B_377, C_375, D_376), B_378))), inference(resolution, [status(thm)], [c_6, c_539])).
% 15.23/6.98  tff(c_52, plain, (![A_183, B_184, C_185, D_186]: (m1_subset_1('#skF_6'(A_183, B_184, C_185, D_186), u1_struct_0(C_185)) | ~r2_hidden(A_183, a_3_0_waybel_9(B_184, C_185, D_186)) | ~m1_subset_1(D_186, u1_struct_0(C_185)) | ~l1_waybel_0(C_185, B_184) | v2_struct_0(C_185) | ~l1_struct_0(B_184) | v2_struct_0(B_184))), inference(cnfTransformation, [status(thm)], [f_110])).
% 15.23/6.98  tff(c_486, plain, (![B_347, C_348, D_349, B_350]: (m1_subset_1('#skF_1'(a_3_0_waybel_9(B_347, C_348, D_349), B_350), u1_struct_0(C_348)) | ~r2_hidden('#skF_1'(a_3_0_waybel_9(B_347, C_348, D_349), B_350), a_3_0_waybel_9(B_347, C_348, D_349)) | ~m1_subset_1(D_349, u1_struct_0(C_348)) | ~l1_waybel_0(C_348, B_347) | v2_struct_0(C_348) | ~l1_struct_0(B_347) | v2_struct_0(B_347) | ~m1_subset_1(D_349, u1_struct_0(C_348)) | ~l1_waybel_0(C_348, B_347) | v2_struct_0(C_348) | ~l1_struct_0(B_347) | v2_struct_0(B_347) | r1_tarski(a_3_0_waybel_9(B_347, C_348, D_349), B_350))), inference(superposition, [status(thm), theory('equality')], [c_150, c_52])).
% 15.23/6.98  tff(c_494, plain, (![B_347, C_348, D_349, B_2]: (m1_subset_1('#skF_1'(a_3_0_waybel_9(B_347, C_348, D_349), B_2), u1_struct_0(C_348)) | ~m1_subset_1(D_349, u1_struct_0(C_348)) | ~l1_waybel_0(C_348, B_347) | v2_struct_0(C_348) | ~l1_struct_0(B_347) | v2_struct_0(B_347) | ~r1_tarski(a_3_0_waybel_9(B_347, C_348, D_349), a_3_0_waybel_9(B_347, C_348, D_349)) | r1_tarski(a_3_0_waybel_9(B_347, C_348, D_349), B_2))), inference(resolution, [status(thm)], [c_85, c_486])).
% 15.23/6.98  tff(c_504, plain, (![B_351, C_352, D_353, B_354]: (m1_subset_1('#skF_1'(a_3_0_waybel_9(B_351, C_352, D_353), B_354), u1_struct_0(C_352)) | ~m1_subset_1(D_353, u1_struct_0(C_352)) | ~l1_waybel_0(C_352, B_351) | v2_struct_0(C_352) | ~l1_struct_0(B_351) | v2_struct_0(B_351) | r1_tarski(a_3_0_waybel_9(B_351, C_352, D_353), B_354))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_494])).
% 15.23/6.98  tff(c_165, plain, (![F_252, A_253, B_254, C_255]: (r2_hidden(F_252, u1_struct_0(k4_waybel_9(A_253, B_254, C_255))) | ~r1_orders_2(B_254, C_255, F_252) | ~m1_subset_1(F_252, u1_struct_0(B_254)) | ~l1_waybel_0(k4_waybel_9(A_253, B_254, C_255), A_253) | ~v6_waybel_0(k4_waybel_9(A_253, B_254, C_255), A_253) | ~m1_subset_1(C_255, u1_struct_0(B_254)) | ~l1_waybel_0(B_254, A_253) | v2_struct_0(B_254) | ~l1_struct_0(A_253) | v2_struct_0(A_253))), inference(cnfTransformation, [status(thm)], [f_73])).
% 15.23/6.98  tff(c_169, plain, (![F_256, A_257, B_258, C_259]: (r2_hidden(F_256, u1_struct_0(k4_waybel_9(A_257, B_258, C_259))) | ~r1_orders_2(B_258, C_259, F_256) | ~m1_subset_1(F_256, u1_struct_0(B_258)) | ~l1_waybel_0(k4_waybel_9(A_257, B_258, C_259), A_257) | ~m1_subset_1(C_259, u1_struct_0(B_258)) | ~l1_waybel_0(B_258, A_257) | v2_struct_0(B_258) | ~l1_struct_0(A_257) | v2_struct_0(A_257))), inference(resolution, [status(thm)], [c_44, c_165])).
% 15.23/6.98  tff(c_171, plain, (![F_256, A_211]: (r2_hidden(F_256, u1_struct_0(k4_waybel_9(A_211, '#skF_8', '#skF_9'))) | ~r1_orders_2('#skF_8', '#skF_9', F_256) | ~m1_subset_1(F_256, u1_struct_0('#skF_8')) | ~m1_subset_1('#skF_9', u1_struct_0('#skF_8')) | v2_struct_0('#skF_8') | ~l1_waybel_0('#skF_8', A_211) | ~l1_struct_0(A_211) | v2_struct_0(A_211))), inference(resolution, [status(thm)], [c_104, c_169])).
% 15.23/6.98  tff(c_174, plain, (![F_256, A_211]: (r2_hidden(F_256, u1_struct_0(k4_waybel_9(A_211, '#skF_8', '#skF_9'))) | ~r1_orders_2('#skF_8', '#skF_9', F_256) | ~m1_subset_1(F_256, u1_struct_0('#skF_8')) | v2_struct_0('#skF_8') | ~l1_waybel_0('#skF_8', A_211) | ~l1_struct_0(A_211) | v2_struct_0(A_211))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_171])).
% 15.23/6.98  tff(c_176, plain, (![F_260, A_261]: (r2_hidden(F_260, u1_struct_0(k4_waybel_9(A_261, '#skF_8', '#skF_9'))) | ~r1_orders_2('#skF_8', '#skF_9', F_260) | ~m1_subset_1(F_260, u1_struct_0('#skF_8')) | ~l1_waybel_0('#skF_8', A_261) | ~l1_struct_0(A_261) | v2_struct_0(A_261))), inference(negUnitSimplification, [status(thm)], [c_60, c_174])).
% 15.23/6.98  tff(c_184, plain, (![A_1, A_261]: (r1_tarski(A_1, u1_struct_0(k4_waybel_9(A_261, '#skF_8', '#skF_9'))) | ~r1_orders_2('#skF_8', '#skF_9', '#skF_1'(A_1, u1_struct_0(k4_waybel_9(A_261, '#skF_8', '#skF_9')))) | ~m1_subset_1('#skF_1'(A_1, u1_struct_0(k4_waybel_9(A_261, '#skF_8', '#skF_9'))), u1_struct_0('#skF_8')) | ~l1_waybel_0('#skF_8', A_261) | ~l1_struct_0(A_261) | v2_struct_0(A_261))), inference(resolution, [status(thm)], [c_176, c_4])).
% 15.23/6.98  tff(c_516, plain, (![B_351, D_353, A_261]: (~r1_orders_2('#skF_8', '#skF_9', '#skF_1'(a_3_0_waybel_9(B_351, '#skF_8', D_353), u1_struct_0(k4_waybel_9(A_261, '#skF_8', '#skF_9')))) | ~l1_waybel_0('#skF_8', A_261) | ~l1_struct_0(A_261) | v2_struct_0(A_261) | ~m1_subset_1(D_353, u1_struct_0('#skF_8')) | ~l1_waybel_0('#skF_8', B_351) | v2_struct_0('#skF_8') | ~l1_struct_0(B_351) | v2_struct_0(B_351) | r1_tarski(a_3_0_waybel_9(B_351, '#skF_8', D_353), u1_struct_0(k4_waybel_9(A_261, '#skF_8', '#skF_9'))))), inference(resolution, [status(thm)], [c_504, c_184])).
% 15.23/6.98  tff(c_528, plain, (![B_351, D_353, A_261]: (~r1_orders_2('#skF_8', '#skF_9', '#skF_1'(a_3_0_waybel_9(B_351, '#skF_8', D_353), u1_struct_0(k4_waybel_9(A_261, '#skF_8', '#skF_9')))) | ~l1_waybel_0('#skF_8', A_261) | ~l1_struct_0(A_261) | v2_struct_0(A_261) | ~m1_subset_1(D_353, u1_struct_0('#skF_8')) | ~l1_waybel_0('#skF_8', B_351) | ~l1_struct_0(B_351) | v2_struct_0(B_351) | r1_tarski(a_3_0_waybel_9(B_351, '#skF_8', D_353), u1_struct_0(k4_waybel_9(A_261, '#skF_8', '#skF_9'))))), inference(negUnitSimplification, [status(thm)], [c_60, c_516])).
% 15.23/6.98  tff(c_582, plain, (![A_261, B_377]: (~l1_waybel_0('#skF_8', A_261) | ~l1_struct_0(A_261) | v2_struct_0(A_261) | ~m1_subset_1('#skF_9', u1_struct_0('#skF_8')) | ~l1_waybel_0('#skF_8', B_377) | v2_struct_0('#skF_8') | ~l1_struct_0(B_377) | v2_struct_0(B_377) | r1_tarski(a_3_0_waybel_9(B_377, '#skF_8', '#skF_9'), u1_struct_0(k4_waybel_9(A_261, '#skF_8', '#skF_9'))))), inference(resolution, [status(thm)], [c_578, c_528])).
% 15.23/6.98  tff(c_590, plain, (![A_261, B_377]: (~l1_waybel_0('#skF_8', A_261) | ~l1_struct_0(A_261) | v2_struct_0(A_261) | ~l1_waybel_0('#skF_8', B_377) | v2_struct_0('#skF_8') | ~l1_struct_0(B_377) | v2_struct_0(B_377) | r1_tarski(a_3_0_waybel_9(B_377, '#skF_8', '#skF_9'), u1_struct_0(k4_waybel_9(A_261, '#skF_8', '#skF_9'))))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_582])).
% 15.23/6.98  tff(c_594, plain, (![A_379, B_380]: (~l1_waybel_0('#skF_8', A_379) | ~l1_struct_0(A_379) | v2_struct_0(A_379) | ~l1_waybel_0('#skF_8', B_380) | ~l1_struct_0(B_380) | v2_struct_0(B_380) | r1_tarski(a_3_0_waybel_9(B_380, '#skF_8', '#skF_9'), u1_struct_0(k4_waybel_9(A_379, '#skF_8', '#skF_9'))))), inference(negUnitSimplification, [status(thm)], [c_60, c_590])).
% 15.23/6.98  tff(c_8, plain, (![B_7, A_6]: (B_7=A_6 | ~r1_tarski(B_7, A_6) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 15.23/6.98  tff(c_612, plain, (![A_379, B_380]: (u1_struct_0(k4_waybel_9(A_379, '#skF_8', '#skF_9'))=a_3_0_waybel_9(B_380, '#skF_8', '#skF_9') | ~r1_tarski(u1_struct_0(k4_waybel_9(A_379, '#skF_8', '#skF_9')), a_3_0_waybel_9(B_380, '#skF_8', '#skF_9')) | ~l1_waybel_0('#skF_8', A_379) | ~l1_struct_0(A_379) | v2_struct_0(A_379) | ~l1_waybel_0('#skF_8', B_380) | ~l1_struct_0(B_380) | v2_struct_0(B_380))), inference(resolution, [status(thm)], [c_594, c_8])).
% 15.23/6.98  tff(c_14804, plain, (![A_807, B_808]: (u1_struct_0(k4_waybel_9(A_807, '#skF_8', '#skF_9'))=a_3_0_waybel_9(B_808, '#skF_8', '#skF_9') | ~l1_waybel_0('#skF_8', B_808) | ~l1_struct_0(B_808) | v2_struct_0(B_808) | ~l1_waybel_0('#skF_8', A_807) | ~l1_struct_0(A_807) | v2_struct_0(A_807))), inference(resolution, [status(thm)], [c_14769, c_612])).
% 15.23/6.98  tff(c_14806, plain, (![A_807]: (u1_struct_0(k4_waybel_9(A_807, '#skF_8', '#skF_9'))=a_3_0_waybel_9('#skF_7', '#skF_8', '#skF_9') | ~l1_struct_0('#skF_7') | v2_struct_0('#skF_7') | ~l1_waybel_0('#skF_8', A_807) | ~l1_struct_0(A_807) | v2_struct_0(A_807))), inference(resolution, [status(thm)], [c_58, c_14804])).
% 15.23/6.98  tff(c_14809, plain, (![A_807]: (u1_struct_0(k4_waybel_9(A_807, '#skF_8', '#skF_9'))=a_3_0_waybel_9('#skF_7', '#skF_8', '#skF_9') | v2_struct_0('#skF_7') | ~l1_waybel_0('#skF_8', A_807) | ~l1_struct_0(A_807) | v2_struct_0(A_807))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_14806])).
% 15.23/6.98  tff(c_14811, plain, (![A_809]: (u1_struct_0(k4_waybel_9(A_809, '#skF_8', '#skF_9'))=a_3_0_waybel_9('#skF_7', '#skF_8', '#skF_9') | ~l1_waybel_0('#skF_8', A_809) | ~l1_struct_0(A_809) | v2_struct_0(A_809))), inference(negUnitSimplification, [status(thm)], [c_64, c_14809])).
% 15.23/6.98  tff(c_54, plain, (u1_struct_0(k4_waybel_9('#skF_7', '#skF_8', '#skF_9'))!=a_3_0_waybel_9('#skF_7', '#skF_8', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_127])).
% 15.23/6.98  tff(c_14934, plain, (~l1_waybel_0('#skF_8', '#skF_7') | ~l1_struct_0('#skF_7') | v2_struct_0('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_14811, c_54])).
% 15.23/6.98  tff(c_14974, plain, (v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_58, c_14934])).
% 15.23/6.98  tff(c_14976, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_14974])).
% 15.23/6.98  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.23/6.98  
% 15.23/6.98  Inference rules
% 15.23/6.98  ----------------------
% 15.23/6.98  #Ref     : 0
% 15.23/6.98  #Sup     : 3215
% 15.23/6.98  #Fact    : 0
% 15.23/6.98  #Define  : 0
% 15.23/6.98  #Split   : 10
% 15.23/6.98  #Chain   : 0
% 15.23/6.98  #Close   : 0
% 15.23/6.98  
% 15.23/6.98  Ordering : KBO
% 15.23/6.98  
% 15.23/6.98  Simplification rules
% 15.23/6.98  ----------------------
% 15.23/6.98  #Subsume      : 993
% 15.23/6.98  #Demod        : 2258
% 15.23/6.98  #Tautology    : 184
% 15.23/6.98  #SimpNegUnit  : 1600
% 15.23/6.98  #BackRed      : 0
% 15.23/6.98  
% 15.23/6.98  #Partial instantiations: 0
% 15.23/6.98  #Strategies tried      : 1
% 15.23/6.98  
% 15.23/6.98  Timing (in seconds)
% 15.23/6.98  ----------------------
% 15.23/6.99  Preprocessing        : 0.35
% 15.23/6.99  Parsing              : 0.16
% 15.23/6.99  CNF conversion       : 0.04
% 15.23/6.99  Main loop            : 5.87
% 15.23/6.99  Inferencing          : 1.15
% 15.23/6.99  Reduction            : 0.93
% 15.23/6.99  Demodulation         : 0.58
% 15.23/6.99  BG Simplification    : 0.17
% 15.23/6.99  Subsumption          : 3.45
% 15.23/6.99  Abstraction          : 0.37
% 15.23/6.99  MUC search           : 0.00
% 15.23/6.99  Cooper               : 0.00
% 15.23/6.99  Total                : 6.27
% 15.23/6.99  Index Insertion      : 0.00
% 15.23/6.99  Index Deletion       : 0.00
% 15.23/6.99  Index Matching       : 0.00
% 15.23/6.99  BG Taut test         : 0.00
%------------------------------------------------------------------------------
