%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT2013+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:38:46 EST 2020

% Result     : Theorem 13.68s
% Output     : CNFRefutation 14.04s
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

tff(f_126,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & l1_struct_0(A) )
       => ! [B] :
            ( ( ~ v2_struct_0(B)
              & l1_waybel_0(B,A) )
           => ! [C] :
                ( m1_subset_1(C,u1_struct_0(B))
               => u1_struct_0(k4_waybel_9(A,B,C)) = a_3_0_waybel_9(A,B,C) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_waybel_9)).

tff(f_88,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A)
        & ~ v2_struct_0(B)
        & l1_waybel_0(B,A)
        & m1_subset_1(C,u1_struct_0(B)) )
     => ( v6_waybel_0(k4_waybel_9(A,B,C),A)
        & l1_waybel_0(k4_waybel_9(A,B,C),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_waybel_9)).

tff(f_30,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_72,axiom,(
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

tff(f_109,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fraenkel_a_3_0_waybel_9)).

tff(c_64,plain,(
    ~ v2_struct_0('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_62,plain,(
    l1_struct_0('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_58,plain,(
    l1_waybel_0('#skF_8','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_60,plain,(
    ~ v2_struct_0('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_56,plain,(
    m1_subset_1('#skF_9',u1_struct_0('#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_99,plain,(
    ! [A_211,B_212,C_213] :
      ( l1_waybel_0(k4_waybel_9(A_211,B_212,C_213),A_211)
      | ~ m1_subset_1(C_213,u1_struct_0(B_212))
      | ~ l1_waybel_0(B_212,A_211)
      | v2_struct_0(B_212)
      | ~ l1_struct_0(A_211)
      | v2_struct_0(A_211) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

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
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_12,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),A_3)
      | r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_82,plain,(
    ! [C_201,B_202,A_203] :
      ( r2_hidden(C_201,B_202)
      | ~ r2_hidden(C_201,A_203)
      | ~ r1_tarski(A_203,B_202) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_85,plain,(
    ! [A_3,B_4,B_202] :
      ( r2_hidden('#skF_1'(A_3,B_4),B_202)
      | ~ r1_tarski(A_3,B_202)
      | r1_tarski(A_3,B_4) ) ),
    inference(resolution,[status(thm)],[c_12,c_82])).

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
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_4101,plain,(
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
    inference(resolution,[status(thm)],[c_12,c_199])).

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
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_12944,plain,(
    ! [A_761,B_762,C_763,B_764] :
      ( m1_subset_1('#skF_1'(u1_struct_0(k4_waybel_9(A_761,B_762,C_763)),B_764),u1_struct_0(B_762))
      | ~ r2_hidden('#skF_1'(u1_struct_0(k4_waybel_9(A_761,B_762,C_763)),B_764),u1_struct_0(k4_waybel_9(A_761,B_762,C_763)))
      | ~ l1_waybel_0(k4_waybel_9(A_761,B_762,C_763),A_761)
      | ~ v6_waybel_0(k4_waybel_9(A_761,B_762,C_763),A_761)
      | ~ m1_subset_1(C_763,u1_struct_0(B_762))
      | ~ l1_waybel_0(B_762,A_761)
      | v2_struct_0(B_762)
      | ~ l1_struct_0(A_761)
      | v2_struct_0(A_761)
      | ~ l1_waybel_0(k4_waybel_9(A_761,B_762,C_763),A_761)
      | ~ v6_waybel_0(k4_waybel_9(A_761,B_762,C_763),A_761)
      | ~ m1_subset_1(C_763,u1_struct_0(B_762))
      | ~ l1_waybel_0(B_762,A_761)
      | v2_struct_0(B_762)
      | ~ l1_struct_0(A_761)
      | v2_struct_0(A_761)
      | r1_tarski(u1_struct_0(k4_waybel_9(A_761,B_762,C_763)),B_764) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4101,c_40])).

tff(c_12956,plain,(
    ! [A_761,B_762,C_763,B_4] :
      ( m1_subset_1('#skF_1'(u1_struct_0(k4_waybel_9(A_761,B_762,C_763)),B_4),u1_struct_0(B_762))
      | ~ l1_waybel_0(k4_waybel_9(A_761,B_762,C_763),A_761)
      | ~ v6_waybel_0(k4_waybel_9(A_761,B_762,C_763),A_761)
      | ~ m1_subset_1(C_763,u1_struct_0(B_762))
      | ~ l1_waybel_0(B_762,A_761)
      | v2_struct_0(B_762)
      | ~ l1_struct_0(A_761)
      | v2_struct_0(A_761)
      | ~ r1_tarski(u1_struct_0(k4_waybel_9(A_761,B_762,C_763)),u1_struct_0(k4_waybel_9(A_761,B_762,C_763)))
      | r1_tarski(u1_struct_0(k4_waybel_9(A_761,B_762,C_763)),B_4) ) ),
    inference(resolution,[status(thm)],[c_85,c_12944])).

tff(c_12970,plain,(
    ! [A_765,B_766,C_767,B_768] :
      ( m1_subset_1('#skF_1'(u1_struct_0(k4_waybel_9(A_765,B_766,C_767)),B_768),u1_struct_0(B_766))
      | ~ l1_waybel_0(k4_waybel_9(A_765,B_766,C_767),A_765)
      | ~ v6_waybel_0(k4_waybel_9(A_765,B_766,C_767),A_765)
      | ~ m1_subset_1(C_767,u1_struct_0(B_766))
      | ~ l1_waybel_0(B_766,A_765)
      | v2_struct_0(B_766)
      | ~ l1_struct_0(A_765)
      | v2_struct_0(A_765)
      | r1_tarski(u1_struct_0(k4_waybel_9(A_765,B_766,C_767)),B_768) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_12956])).

tff(c_12974,plain,(
    ! [A_769,B_770,C_771,B_772] :
      ( m1_subset_1('#skF_1'(u1_struct_0(k4_waybel_9(A_769,B_770,C_771)),B_772),u1_struct_0(B_770))
      | ~ l1_waybel_0(k4_waybel_9(A_769,B_770,C_771),A_769)
      | r1_tarski(u1_struct_0(k4_waybel_9(A_769,B_770,C_771)),B_772)
      | ~ m1_subset_1(C_771,u1_struct_0(B_770))
      | ~ l1_waybel_0(B_770,A_769)
      | v2_struct_0(B_770)
      | ~ l1_struct_0(A_769)
      | v2_struct_0(A_769) ) ),
    inference(resolution,[status(thm)],[c_44,c_12970])).

tff(c_12988,plain,(
    ! [A_211,B_772] :
      ( m1_subset_1('#skF_1'(u1_struct_0(k4_waybel_9(A_211,'#skF_8','#skF_9')),B_772),u1_struct_0('#skF_8'))
      | r1_tarski(u1_struct_0(k4_waybel_9(A_211,'#skF_8','#skF_9')),B_772)
      | ~ m1_subset_1('#skF_9',u1_struct_0('#skF_8'))
      | v2_struct_0('#skF_8')
      | ~ l1_waybel_0('#skF_8',A_211)
      | ~ l1_struct_0(A_211)
      | v2_struct_0(A_211) ) ),
    inference(resolution,[status(thm)],[c_104,c_12974])).

tff(c_13003,plain,(
    ! [A_211,B_772] :
      ( m1_subset_1('#skF_1'(u1_struct_0(k4_waybel_9(A_211,'#skF_8','#skF_9')),B_772),u1_struct_0('#skF_8'))
      | r1_tarski(u1_struct_0(k4_waybel_9(A_211,'#skF_8','#skF_9')),B_772)
      | v2_struct_0('#skF_8')
      | ~ l1_waybel_0('#skF_8',A_211)
      | ~ l1_struct_0(A_211)
      | v2_struct_0(A_211) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_12988])).

tff(c_13004,plain,(
    ! [A_211,B_772] :
      ( m1_subset_1('#skF_1'(u1_struct_0(k4_waybel_9(A_211,'#skF_8','#skF_9')),B_772),u1_struct_0('#skF_8'))
      | r1_tarski(u1_struct_0(k4_waybel_9(A_211,'#skF_8','#skF_9')),B_772)
      | ~ l1_waybel_0('#skF_8',A_211)
      | ~ l1_struct_0(A_211)
      | v2_struct_0(A_211) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_13003])).

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
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_13419,plain,(
    ! [B_788,C_789,A_790,B_791] :
      ( r1_orders_2(B_788,C_789,'#skF_1'(u1_struct_0(k4_waybel_9(A_790,B_788,C_789)),B_791))
      | ~ r2_hidden('#skF_1'(u1_struct_0(k4_waybel_9(A_790,B_788,C_789)),B_791),u1_struct_0(k4_waybel_9(A_790,B_788,C_789)))
      | ~ l1_waybel_0(k4_waybel_9(A_790,B_788,C_789),A_790)
      | ~ v6_waybel_0(k4_waybel_9(A_790,B_788,C_789),A_790)
      | ~ m1_subset_1(C_789,u1_struct_0(B_788))
      | ~ l1_waybel_0(B_788,A_790)
      | v2_struct_0(B_788)
      | ~ l1_struct_0(A_790)
      | v2_struct_0(A_790)
      | ~ l1_waybel_0(k4_waybel_9(A_790,B_788,C_789),A_790)
      | ~ v6_waybel_0(k4_waybel_9(A_790,B_788,C_789),A_790)
      | ~ m1_subset_1(C_789,u1_struct_0(B_788))
      | ~ l1_waybel_0(B_788,A_790)
      | v2_struct_0(B_788)
      | ~ l1_struct_0(A_790)
      | v2_struct_0(A_790)
      | r1_tarski(u1_struct_0(k4_waybel_9(A_790,B_788,C_789)),B_791) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4101,c_36])).

tff(c_13431,plain,(
    ! [B_788,C_789,A_790,B_4] :
      ( r1_orders_2(B_788,C_789,'#skF_1'(u1_struct_0(k4_waybel_9(A_790,B_788,C_789)),B_4))
      | ~ l1_waybel_0(k4_waybel_9(A_790,B_788,C_789),A_790)
      | ~ v6_waybel_0(k4_waybel_9(A_790,B_788,C_789),A_790)
      | ~ m1_subset_1(C_789,u1_struct_0(B_788))
      | ~ l1_waybel_0(B_788,A_790)
      | v2_struct_0(B_788)
      | ~ l1_struct_0(A_790)
      | v2_struct_0(A_790)
      | ~ r1_tarski(u1_struct_0(k4_waybel_9(A_790,B_788,C_789)),u1_struct_0(k4_waybel_9(A_790,B_788,C_789)))
      | r1_tarski(u1_struct_0(k4_waybel_9(A_790,B_788,C_789)),B_4) ) ),
    inference(resolution,[status(thm)],[c_85,c_13419])).

tff(c_13445,plain,(
    ! [B_792,C_793,A_794,B_795] :
      ( r1_orders_2(B_792,C_793,'#skF_1'(u1_struct_0(k4_waybel_9(A_794,B_792,C_793)),B_795))
      | ~ l1_waybel_0(k4_waybel_9(A_794,B_792,C_793),A_794)
      | ~ v6_waybel_0(k4_waybel_9(A_794,B_792,C_793),A_794)
      | ~ m1_subset_1(C_793,u1_struct_0(B_792))
      | ~ l1_waybel_0(B_792,A_794)
      | v2_struct_0(B_792)
      | ~ l1_struct_0(A_794)
      | v2_struct_0(A_794)
      | r1_tarski(u1_struct_0(k4_waybel_9(A_794,B_792,C_793)),B_795) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_13431])).

tff(c_13449,plain,(
    ! [B_796,C_797,A_798,B_799] :
      ( r1_orders_2(B_796,C_797,'#skF_1'(u1_struct_0(k4_waybel_9(A_798,B_796,C_797)),B_799))
      | ~ l1_waybel_0(k4_waybel_9(A_798,B_796,C_797),A_798)
      | r1_tarski(u1_struct_0(k4_waybel_9(A_798,B_796,C_797)),B_799)
      | ~ m1_subset_1(C_797,u1_struct_0(B_796))
      | ~ l1_waybel_0(B_796,A_798)
      | v2_struct_0(B_796)
      | ~ l1_struct_0(A_798)
      | v2_struct_0(A_798) ) ),
    inference(resolution,[status(thm)],[c_44,c_13445])).

tff(c_13465,plain,(
    ! [A_211,B_799] :
      ( r1_orders_2('#skF_8','#skF_9','#skF_1'(u1_struct_0(k4_waybel_9(A_211,'#skF_8','#skF_9')),B_799))
      | r1_tarski(u1_struct_0(k4_waybel_9(A_211,'#skF_8','#skF_9')),B_799)
      | ~ m1_subset_1('#skF_9',u1_struct_0('#skF_8'))
      | v2_struct_0('#skF_8')
      | ~ l1_waybel_0('#skF_8',A_211)
      | ~ l1_struct_0(A_211)
      | v2_struct_0(A_211) ) ),
    inference(resolution,[status(thm)],[c_104,c_13449])).

tff(c_13483,plain,(
    ! [A_211,B_799] :
      ( r1_orders_2('#skF_8','#skF_9','#skF_1'(u1_struct_0(k4_waybel_9(A_211,'#skF_8','#skF_9')),B_799))
      | r1_tarski(u1_struct_0(k4_waybel_9(A_211,'#skF_8','#skF_9')),B_799)
      | v2_struct_0('#skF_8')
      | ~ l1_waybel_0('#skF_8',A_211)
      | ~ l1_struct_0(A_211)
      | v2_struct_0(A_211) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_13465])).

tff(c_13485,plain,(
    ! [A_800,B_801] :
      ( r1_orders_2('#skF_8','#skF_9','#skF_1'(u1_struct_0(k4_waybel_9(A_800,'#skF_8','#skF_9')),B_801))
      | r1_tarski(u1_struct_0(k4_waybel_9(A_800,'#skF_8','#skF_9')),B_801)
      | ~ l1_waybel_0('#skF_8',A_800)
      | ~ l1_struct_0(A_800)
      | v2_struct_0(A_800) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_13483])).

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
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_10,plain,(
    ! [A_3,B_4] :
      ( ~ r2_hidden('#skF_1'(A_3,B_4),B_4)
      | r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_134,plain,(
    ! [A_3,B_227,C_228,D_229] :
      ( r1_tarski(A_3,a_3_0_waybel_9(B_227,C_228,D_229))
      | ~ r1_orders_2(C_228,D_229,'#skF_1'(A_3,a_3_0_waybel_9(B_227,C_228,D_229)))
      | ~ m1_subset_1('#skF_1'(A_3,a_3_0_waybel_9(B_227,C_228,D_229)),u1_struct_0(C_228))
      | ~ m1_subset_1(D_229,u1_struct_0(C_228))
      | ~ l1_waybel_0(C_228,B_227)
      | v2_struct_0(C_228)
      | ~ l1_struct_0(B_227)
      | v2_struct_0(B_227) ) ),
    inference(resolution,[status(thm)],[c_122,c_10])).

tff(c_13498,plain,(
    ! [A_800,B_227] :
      ( ~ m1_subset_1('#skF_1'(u1_struct_0(k4_waybel_9(A_800,'#skF_8','#skF_9')),a_3_0_waybel_9(B_227,'#skF_8','#skF_9')),u1_struct_0('#skF_8'))
      | ~ m1_subset_1('#skF_9',u1_struct_0('#skF_8'))
      | ~ l1_waybel_0('#skF_8',B_227)
      | v2_struct_0('#skF_8')
      | ~ l1_struct_0(B_227)
      | v2_struct_0(B_227)
      | r1_tarski(u1_struct_0(k4_waybel_9(A_800,'#skF_8','#skF_9')),a_3_0_waybel_9(B_227,'#skF_8','#skF_9'))
      | ~ l1_waybel_0('#skF_8',A_800)
      | ~ l1_struct_0(A_800)
      | v2_struct_0(A_800) ) ),
    inference(resolution,[status(thm)],[c_13485,c_134])).

tff(c_13506,plain,(
    ! [A_800,B_227] :
      ( ~ m1_subset_1('#skF_1'(u1_struct_0(k4_waybel_9(A_800,'#skF_8','#skF_9')),a_3_0_waybel_9(B_227,'#skF_8','#skF_9')),u1_struct_0('#skF_8'))
      | ~ l1_waybel_0('#skF_8',B_227)
      | v2_struct_0('#skF_8')
      | ~ l1_struct_0(B_227)
      | v2_struct_0(B_227)
      | r1_tarski(u1_struct_0(k4_waybel_9(A_800,'#skF_8','#skF_9')),a_3_0_waybel_9(B_227,'#skF_8','#skF_9'))
      | ~ l1_waybel_0('#skF_8',A_800)
      | ~ l1_struct_0(A_800)
      | v2_struct_0(A_800) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_13498])).

tff(c_13512,plain,(
    ! [A_802,B_803] :
      ( ~ m1_subset_1('#skF_1'(u1_struct_0(k4_waybel_9(A_802,'#skF_8','#skF_9')),a_3_0_waybel_9(B_803,'#skF_8','#skF_9')),u1_struct_0('#skF_8'))
      | ~ l1_waybel_0('#skF_8',B_803)
      | ~ l1_struct_0(B_803)
      | v2_struct_0(B_803)
      | r1_tarski(u1_struct_0(k4_waybel_9(A_802,'#skF_8','#skF_9')),a_3_0_waybel_9(B_803,'#skF_8','#skF_9'))
      | ~ l1_waybel_0('#skF_8',A_802)
      | ~ l1_struct_0(A_802)
      | v2_struct_0(A_802) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_13506])).

tff(c_13518,plain,(
    ! [B_804,A_805] :
      ( ~ l1_waybel_0('#skF_8',B_804)
      | ~ l1_struct_0(B_804)
      | v2_struct_0(B_804)
      | r1_tarski(u1_struct_0(k4_waybel_9(A_805,'#skF_8','#skF_9')),a_3_0_waybel_9(B_804,'#skF_8','#skF_9'))
      | ~ l1_waybel_0('#skF_8',A_805)
      | ~ l1_struct_0(A_805)
      | v2_struct_0(A_805) ) ),
    inference(resolution,[status(thm)],[c_13004,c_13512])).

tff(c_107,plain,(
    ! [A_218,B_219,C_220,D_221] :
      ( '#skF_6'(A_218,B_219,C_220,D_221) = A_218
      | ~ r2_hidden(A_218,a_3_0_waybel_9(B_219,C_220,D_221))
      | ~ m1_subset_1(D_221,u1_struct_0(C_220))
      | ~ l1_waybel_0(C_220,B_219)
      | v2_struct_0(C_220)
      | ~ l1_struct_0(B_219)
      | v2_struct_0(B_219) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_150,plain,(
    ! [B_248,C_249,D_250,B_251] :
      ( '#skF_6'('#skF_1'(a_3_0_waybel_9(B_248,C_249,D_250),B_251),B_248,C_249,D_250) = '#skF_1'(a_3_0_waybel_9(B_248,C_249,D_250),B_251)
      | ~ m1_subset_1(D_250,u1_struct_0(C_249))
      | ~ l1_waybel_0(C_249,B_248)
      | v2_struct_0(C_249)
      | ~ l1_struct_0(B_248)
      | v2_struct_0(B_248)
      | r1_tarski(a_3_0_waybel_9(B_248,C_249,D_250),B_251) ) ),
    inference(resolution,[status(thm)],[c_12,c_107])).

tff(c_48,plain,(
    ! [C_185,D_186,A_183,B_184] :
      ( r1_orders_2(C_185,D_186,'#skF_6'(A_183,B_184,C_185,D_186))
      | ~ r2_hidden(A_183,a_3_0_waybel_9(B_184,C_185,D_186))
      | ~ m1_subset_1(D_186,u1_struct_0(C_185))
      | ~ l1_waybel_0(C_185,B_184)
      | v2_struct_0(C_185)
      | ~ l1_struct_0(B_184)
      | v2_struct_0(B_184) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

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
    inference(resolution,[status(thm)],[c_12,c_539])).

tff(c_52,plain,(
    ! [A_183,B_184,C_185,D_186] :
      ( m1_subset_1('#skF_6'(A_183,B_184,C_185,D_186),u1_struct_0(C_185))
      | ~ r2_hidden(A_183,a_3_0_waybel_9(B_184,C_185,D_186))
      | ~ m1_subset_1(D_186,u1_struct_0(C_185))
      | ~ l1_waybel_0(C_185,B_184)
      | v2_struct_0(C_185)
      | ~ l1_struct_0(B_184)
      | v2_struct_0(B_184) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

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
    ! [B_347,C_348,D_349,B_4] :
      ( m1_subset_1('#skF_1'(a_3_0_waybel_9(B_347,C_348,D_349),B_4),u1_struct_0(C_348))
      | ~ m1_subset_1(D_349,u1_struct_0(C_348))
      | ~ l1_waybel_0(C_348,B_347)
      | v2_struct_0(C_348)
      | ~ l1_struct_0(B_347)
      | v2_struct_0(B_347)
      | ~ r1_tarski(a_3_0_waybel_9(B_347,C_348,D_349),a_3_0_waybel_9(B_347,C_348,D_349))
      | r1_tarski(a_3_0_waybel_9(B_347,C_348,D_349),B_4) ) ),
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
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_494])).

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
    inference(cnfTransformation,[status(thm)],[f_72])).

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
    ! [A_3,A_261] :
      ( r1_tarski(A_3,u1_struct_0(k4_waybel_9(A_261,'#skF_8','#skF_9')))
      | ~ r1_orders_2('#skF_8','#skF_9','#skF_1'(A_3,u1_struct_0(k4_waybel_9(A_261,'#skF_8','#skF_9'))))
      | ~ m1_subset_1('#skF_1'(A_3,u1_struct_0(k4_waybel_9(A_261,'#skF_8','#skF_9'))),u1_struct_0('#skF_8'))
      | ~ l1_waybel_0('#skF_8',A_261)
      | ~ l1_struct_0(A_261)
      | v2_struct_0(A_261) ) ),
    inference(resolution,[status(thm)],[c_176,c_10])).

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

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

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
    inference(resolution,[status(thm)],[c_594,c_2])).

tff(c_13553,plain,(
    ! [A_806,B_807] :
      ( u1_struct_0(k4_waybel_9(A_806,'#skF_8','#skF_9')) = a_3_0_waybel_9(B_807,'#skF_8','#skF_9')
      | ~ l1_waybel_0('#skF_8',B_807)
      | ~ l1_struct_0(B_807)
      | v2_struct_0(B_807)
      | ~ l1_waybel_0('#skF_8',A_806)
      | ~ l1_struct_0(A_806)
      | v2_struct_0(A_806) ) ),
    inference(resolution,[status(thm)],[c_13518,c_612])).

tff(c_13555,plain,(
    ! [A_806] :
      ( u1_struct_0(k4_waybel_9(A_806,'#skF_8','#skF_9')) = a_3_0_waybel_9('#skF_7','#skF_8','#skF_9')
      | ~ l1_struct_0('#skF_7')
      | v2_struct_0('#skF_7')
      | ~ l1_waybel_0('#skF_8',A_806)
      | ~ l1_struct_0(A_806)
      | v2_struct_0(A_806) ) ),
    inference(resolution,[status(thm)],[c_58,c_13553])).

tff(c_13558,plain,(
    ! [A_806] :
      ( u1_struct_0(k4_waybel_9(A_806,'#skF_8','#skF_9')) = a_3_0_waybel_9('#skF_7','#skF_8','#skF_9')
      | v2_struct_0('#skF_7')
      | ~ l1_waybel_0('#skF_8',A_806)
      | ~ l1_struct_0(A_806)
      | v2_struct_0(A_806) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_13555])).

tff(c_13560,plain,(
    ! [A_808] :
      ( u1_struct_0(k4_waybel_9(A_808,'#skF_8','#skF_9')) = a_3_0_waybel_9('#skF_7','#skF_8','#skF_9')
      | ~ l1_waybel_0('#skF_8',A_808)
      | ~ l1_struct_0(A_808)
      | v2_struct_0(A_808) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_13558])).

tff(c_54,plain,(
    u1_struct_0(k4_waybel_9('#skF_7','#skF_8','#skF_9')) != a_3_0_waybel_9('#skF_7','#skF_8','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_13695,plain,
    ( ~ l1_waybel_0('#skF_8','#skF_7')
    | ~ l1_struct_0('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_13560,c_54])).

tff(c_13735,plain,(
    v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_58,c_13695])).

tff(c_13737,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_13735])).

%------------------------------------------------------------------------------
